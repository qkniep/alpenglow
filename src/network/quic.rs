// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! QUIC network interface — **draft scaffold behind the `quic` feature**.
//!
//! Implements the datagram-mode side of [`Network`] over quinn (RFC 9221
//! unreliable datagrams), giving every message an authenticated, spoof-proof
//! origin: the peer proves it holds a validator's Ed25519 identity key during
//! the TLS 1.3 handshake, so [`PeerId::validator`] is trustworthy and
//! [`Network::ban`] can reliably shun a misbehaving validator.
//!
//! This is the all-to-all / disseminator / repair transport. Transaction
//! ingestion wants QUIC *streams* (reliable, ordered, flow-controlled) and
//! belongs behind a separate `Ingest` trait sharing the same [`Endpoint`].
//!
//! # Status
//!
//! Compiled only under `--features quic`, so the default UDP build is
//! unaffected. The transport plumbing is complete; what remains is the crypto
//! core in the [`tls`] module (marked with `todo!`): self-signed certificate
//! generation from the node's Ed25519 key (via `rcgen`), and the two rustls
//! verifier bodies that gate the handshake against the validator set.
//!
//! # Performance
//!
//! QUIC datagrams cost more than the tuned UDP path on the broadcast hot path:
//! per-datagram AEAD, no cross-destination `sendmmsg` batching, and N² live
//! connections. Prefer this for authenticated ingress; benchmark before moving
//! the all-to-all/disseminator planes off [`UdpNetwork`](super::UdpNetwork).

use std::collections::{HashMap, HashSet};
use std::io;
use std::marker::PhantomData;
use std::net::SocketAddr;
use std::sync::Arc;

use async_trait::async_trait;
use bytes::Bytes;
use log::warn;
use quinn::rustls::pki_types::CertificateDer;
use quinn::{Connection, Endpoint};
use tokio::sync::{Mutex, RwLock, mpsc};
use wincode::config::DefaultConfig;
use wincode::{SchemaRead, SchemaWrite};

use super::{Network, NetworkMessageConfig, PeerId};
use crate::ValidatorIndex;

/// Placeholder SNI server name. Ignored — [`PeerVerifier`] authenticates by the
/// certificate's embedded validator key, not by hostname.
const SERVER_NAME: &str = "alpenglow";

/// Capacity of the channel buffering inbound datagrams across all connections.
const INBOUND_CAPACITY: usize = 1024;

/// Authenticated identity of a QUIC peer.
///
/// Produced only after the handshake proves the peer holds the Ed25519 key of a
/// validator in the current epoch, so [`validator`](PeerId::validator) is a
/// spoof-proof origin the caller can attribute and ban.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthPeer {
    validator: ValidatorIndex,
    addr: SocketAddr,
}

impl PeerId for AuthPeer {
    fn validator(&self) -> Option<ValidatorIndex> {
        Some(self.validator)
    }
}

/// Resolves a handshaking peer's certificate to a validator identity.
///
/// This is the admission-control policy, injected so the network layer stays
/// decoupled from the validator set. A closed-set implementation backed by
/// `EpochInfo` accepts only certs whose embedded key belongs to a current
/// validator; an open/stake-weighted implementation suits client ingestion.
pub trait PeerVerifier: Send + Sync + 'static {
    /// Returns the validator the certificate proves, or `None` to reject the
    /// connection (unknown key, malformed cert, failed self-signature check).
    fn resolve(&self, cert: &CertificateDer<'_>, addr: SocketAddr) -> Option<ValidatorIndex>;
}

/// [`Network`] implementation over authenticated QUIC datagrams.
pub struct QuicNetwork<S, R> {
    /// Single UDP socket underneath; hosts every connection, both roles.
    endpoint: Endpoint,
    /// Live connection per peer address, dialed lazily and kept warm.
    // NOTE: a simultaneous dial from both sides can transiently open two
    // connections to one peer; last writer wins here. Acceptable for datagrams.
    conns: Arc<RwLock<HashMap<SocketAddr, Connection>>>,
    /// Maps a handshaking certificate to a validator, or rejects it.
    verifier: Arc<dyn PeerVerifier>,
    /// Validators barred by the app after provable misbehavior.
    banned: Arc<RwLock<HashSet<ValidatorIndex>>>,
    /// Sender half handed to every per-connection reader task.
    inbound_tx: mpsc::Sender<(AuthPeer, R)>,
    /// Receiver drained by [`receive_from`](Network::receive_from).
    inbound_rx: Mutex<mpsc::Receiver<(AuthPeer, R)>>,
    _msg: PhantomData<fn() -> S>,
}

impl<S, R> QuicNetwork<S, R>
where
    R: for<'de> SchemaRead<'de, NetworkMessageConfig, Dst = R> + Send + 'static,
{
    /// Creates a QUIC network bound to `port`, presenting `cert`/`key` as this
    /// node's validator identity and admitting peers per `verifier`.
    ///
    /// # Errors
    ///
    /// Returns an error if the socket cannot be bound or the TLS config is
    /// rejected by quinn (e.g. missing a TLS 1.3 initial cipher suite).
    pub fn new(
        port: u16,
        cert: CertificateDer<'static>,
        key: quinn::rustls::pki_types::PrivateKeyDer<'static>,
        verifier: Arc<dyn PeerVerifier>,
    ) -> io::Result<Self> {
        let server_config = tls::server_config(cert.clone(), key.clone_key(), verifier.clone())?;
        let client_config = tls::client_config(cert, key, verifier.clone())?;

        let bind = SocketAddr::new(std::net::Ipv4Addr::UNSPECIFIED.into(), port);
        let mut endpoint = Endpoint::server(server_config, bind)?;
        endpoint.set_default_client_config(client_config);

        let (inbound_tx, inbound_rx) = mpsc::channel(INBOUND_CAPACITY);
        let net = Self {
            endpoint,
            conns: Arc::new(RwLock::new(HashMap::new())),
            verifier,
            banned: Arc::new(RwLock::new(HashSet::new())),
            inbound_tx,
            inbound_rx: Mutex::new(inbound_rx),
            _msg: PhantomData,
        };
        net.spawn_accept_loop();
        Ok(net)
    }

    /// Returns the local UDP port the endpoint is bound to.
    pub fn port(&self) -> u16 {
        self.endpoint
            .local_addr()
            .expect("bound endpoint has a local address")
            .port()
    }

    /// Spawns the background task that accepts inbound connections, authenticates
    /// each, and pumps its datagrams into `inbound_tx`.
    fn spawn_accept_loop(&self) {
        let endpoint = self.endpoint.clone();
        let conns = self.conns.clone();
        let verifier = self.verifier.clone();
        let banned = self.banned.clone();
        let tx = self.inbound_tx.clone();

        tokio::spawn(async move {
            while let Some(incoming) = endpoint.accept().await {
                let (conns, verifier, banned, tx) =
                    (conns.clone(), verifier.clone(), banned.clone(), tx.clone());
                tokio::spawn(async move {
                    let conn = match incoming.await {
                        Ok(conn) => conn,
                        Err(err) => {
                            warn!("inbound QUIC handshake failed: {err}");
                            return;
                        }
                    };
                    let Some(peer) = authenticate(&conn, &*verifier, &banned).await else {
                        conn.close(0u32.into(), b"unauthorized");
                        return;
                    };
                    conns.write().await.insert(peer.addr, conn.clone());
                    read_datagrams(conn, peer, tx).await;
                });
            }
        });
    }

    /// Returns a live connection to `addr`, dialing and authenticating one if
    /// none is cached (or the cached one has closed).
    async fn connection(&self, addr: SocketAddr) -> io::Result<Connection> {
        // clone the handle out so the read guard is not held past this statement
        let cached = self.conns.read().await.get(&addr).cloned();
        if let Some(conn) = cached
            && conn.close_reason().is_none()
        {
            return Ok(conn);
        }

        // NOTE: awaiting the handshake here adds ~1-RTT to the first datagram to
        // a cold peer. A production build should pre-warm the validator mesh at
        // epoch start so steady-state sends never pay this.
        let conn = self
            .endpoint
            .connect(addr, SERVER_NAME)
            .map_err(io::Error::other)?
            .await
            .map_err(io::Error::other)?;
        let Some(peer) = authenticate(&conn, &*self.verifier, &self.banned).await else {
            conn.close(0u32.into(), b"unauthorized");
            return Err(io::Error::other("peer failed validator authentication"));
        };

        self.conns.write().await.insert(addr, conn.clone());
        tokio::spawn(read_datagrams(conn.clone(), peer, self.inbound_tx.clone()));
        Ok(conn)
    }

    /// Serializes and sends `msg` as one unreliable datagram over `conn`.
    fn send_datagram(&self, conn: &Connection, msg: &S) -> io::Result<()>
    where
        S: SchemaWrite<DefaultConfig, Src = S>,
    {
        let bytes = crate::serialize(msg);
        if let Some(max) = conn.max_datagram_size() {
            // NOTE: MTU_BYTES budgeting must leave headroom for QUIC + AEAD
            // overhead; a datagram over this limit is refused, not fragmented.
            assert!(bytes.len() <= max, "message exceeds QUIC datagram limit");
        }
        conn.send_datagram(Bytes::from(bytes))
            .map_err(io::Error::other)
    }
}

#[async_trait]
impl<S, R> Network for QuicNetwork<S, R>
where
    S: SchemaWrite<DefaultConfig, Src = S> + Send + Sync,
    R: for<'de> SchemaRead<'de, NetworkMessageConfig, Dst = R> + Send + Sync + 'static,
{
    type Peer = AuthPeer;
    type Recv = R;
    type Send = S;

    async fn send_to_many(
        &self,
        msg: &S,
        addrs: impl IntoIterator<Item = SocketAddr> + Send,
    ) -> io::Result<()> {
        // collect before the first `.await` so the future stays `Send`
        let addrs: Vec<SocketAddr> = addrs.into_iter().collect();

        // best-effort: attempt every peer, surface the first error afterwards
        let mut first_err = None;
        for addr in addrs {
            let res = match self.connection(addr).await {
                Ok(conn) => self.send_datagram(&conn, msg),
                Err(err) => Err(err),
            };
            if let Err(err) = res {
                warn!("QUIC send to {addr} failed: {err}");
                first_err.get_or_insert(err);
            }
        }
        first_err.map_or(Ok(()), Err)
    }

    async fn send(&self, msg: &S, addr: SocketAddr) -> io::Result<()> {
        let conn = self.connection(addr).await?;
        self.send_datagram(&conn, msg)
    }

    async fn receive_from(&self) -> io::Result<(AuthPeer, R)> {
        self.inbound_rx
            .lock()
            .await
            .recv()
            .await
            .ok_or_else(|| io::Error::other("all QUIC connections closed"))
    }

    fn ban(&self, peer: &AuthPeer) {
        // Sync signature: record the ban and close the connection off-task.
        let (validator, addr) = (peer.validator, peer.addr);
        let banned = self.banned.clone();
        let conns = self.conns.clone();
        tokio::spawn(async move {
            banned.write().await.insert(validator);
            if let Some(conn) = conns.write().await.remove(&addr) {
                conn.close(0u32.into(), b"banned");
            }
        });
    }
}

/// Extracts the peer's validator identity from a completed connection.
///
/// Returns `None` (caller closes the connection) if the peer presented no
/// certificate, the certificate does not resolve to a validator, or that
/// validator is currently banned.
async fn authenticate(
    conn: &Connection,
    verifier: &dyn PeerVerifier,
    banned: &RwLock<HashSet<ValidatorIndex>>,
) -> Option<AuthPeer> {
    let identity = conn.peer_identity()?;
    let certs = identity.downcast::<Vec<CertificateDer<'static>>>().ok()?;
    let validator = verifier.resolve(certs.first()?, conn.remote_address())?;
    if banned.read().await.contains(&validator) {
        return None;
    }
    Some(AuthPeer {
        validator,
        addr: conn.remote_address(),
    })
}

/// Reads datagrams off `conn` until it closes, forwarding each decoded message
/// with its authenticated origin into `tx`.
async fn read_datagrams<R>(conn: Connection, peer: AuthPeer, tx: mpsc::Sender<(AuthPeer, R)>)
where
    R: for<'de> SchemaRead<'de, NetworkMessageConfig, Dst = R>,
{
    loop {
        match conn.read_datagram().await {
            Ok(bytes) => match crate::network::deserialize::<R>(&bytes) {
                Ok(msg) => {
                    if tx.send((peer, msg)).await.is_err() {
                        return; // receiver dropped: network is shutting down
                    }
                }
                Err(err) => warn!(
                    "dropping malformed datagram from {:?}: {err}",
                    peer.validator
                ),
            },
            // connection closed or lost: stop reading
            Err(_) => return,
        }
    }
}

/// rustls plumbing: builds QUIC-compatible TLS configs whose peer verification
/// is delegated to a [`PeerVerifier`].
mod tls {
    use std::sync::Arc;

    use quinn::rustls::pki_types::{CertificateDer, PrivateKeyDer};
    use quinn::{ClientConfig, ServerConfig};

    use super::PeerVerifier;

    /// ALPN protocol identifier negotiated during the TLS handshake.
    const ALPN: &[u8] = b"alpenglow/1";

    /// Builds the server-side config: presents `cert`/`key` and requires every
    /// client to present a validator certificate (mutual TLS).
    ///
    /// # Errors
    ///
    /// Currently always errors: the validator-set verifier is not yet
    /// implemented, so enabling `quic` and constructing a [`QuicNetwork`] fails
    /// with a clear message rather than serving unauthenticated connections.
    ///
    /// [`QuicNetwork`]: super::QuicNetwork
    pub(super) fn server_config(
        _cert: CertificateDer<'static>,
        _key: PrivateKeyDer<'static>,
        _verifier: Arc<dyn PeerVerifier>,
    ) -> std::io::Result<ServerConfig> {
        // Build a rustls::ServerConfig::builder()
        //   .with_client_cert_verifier(Arc::new(ValidatorClientVerifier(verifier)))
        //   .with_single_cert(vec![cert], key)?; set alpn_protocols = [ALPN.to_vec()];
        // then: ServerConfig::with_crypto(Arc::new(QuicServerConfig::try_from(rustls)?)).
        let _ = ALPN;
        Err(std::io::Error::other(
            "QUIC server TLS config not yet implemented (see network::quic::tls)",
        ))
    }

    /// Builds the client-side config: presents `cert`/`key` and verifies the
    /// server's certificate against the validator set.
    ///
    /// # Errors
    ///
    /// Currently always errors; see [`server_config`].
    pub(super) fn client_config(
        _cert: CertificateDer<'static>,
        _key: PrivateKeyDer<'static>,
        _verifier: Arc<dyn PeerVerifier>,
    ) -> std::io::Result<ClientConfig> {
        // Build a rustls::ClientConfig::builder()
        //   .dangerous().with_custom_certificate_verifier(Arc::new(ValidatorServerVerifier(verifier)))
        //   .with_client_auth_cert(vec![cert], key)?; set alpn_protocols = [ALPN.to_vec()];
        // then: ClientConfig::new(Arc::new(QuicClientConfig::try_from(rustls)?)).
        Err(std::io::Error::other(
            "QUIC client TLS config not yet implemented (see network::quic::tls)",
        ))
    }

    // TODO: implement the two rustls verifier newtypes over `Arc<dyn PeerVerifier>`:
    //   - `rustls::server::danger::ClientCertVerifier` for the server side, and
    //   - `rustls::client::danger::ServerCertVerifier` for the client side.
    // Each must: verify the presented cert is a well-formed self-signed
    // Ed25519 cert, then accept only if `verifier.resolve(cert, _)` is `Some`.
    // The identity→ValidatorIndex lookup also runs post-handshake in
    // `authenticate`, so the verifier's job is purely admission control.
}
