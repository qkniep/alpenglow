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
//! unaffected. Identity binds to the validator's Ed25519 consensus key: the node
//! presents a self-signed certificate over that key ([`self_signed_identity`]),
//! and [`PubkeyDirectory`] admits a peer only if its certificate's key belongs to
//! a validator in the set. Remaining work is production hardening: connection
//! pre-warming, epoch-transition churn, and a stream-mode ingestion path.
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
use quinn::rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use quinn::{Connection, Endpoint};
use tokio::sync::{Mutex, RwLock, mpsc};
use wincode::config::DefaultConfig;
use wincode::{SchemaRead, SchemaWrite};

use super::{Network, NetworkMessageConfig, PeerId};
use crate::crypto::signature::{PublicKey, SecretKey};
use crate::{ValidatorIndex, ValidatorInfo};

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
/// decoupled from the validator set. [`PubkeyDirectory`] is the closed-set
/// implementation for the validator mesh; an open/stake-weighted implementation
/// would suit client ingestion.
pub trait PeerVerifier: std::fmt::Debug + Send + Sync + 'static {
    /// Returns the validator whose Ed25519 key the certificate carries, or
    /// `None` to reject the connection (unknown key, or malformed / non-Ed25519
    /// certificate).
    ///
    /// Possession of the key is proven separately by the TLS handshake, so an
    /// implementation only needs to check set membership, not the signature.
    fn resolve(&self, cert: &CertificateDer<'_>) -> Option<ValidatorIndex>;
}

/// A [`PeerVerifier`] backed by a fixed set of validator public keys.
///
/// The closed-set admission policy for the validator mesh: a connection is
/// accepted only if its certificate's Ed25519 key belongs to a validator in the
/// directory. Build one per epoch from
/// [`EpochInfo`](crate::consensus::EpochInfo)'s validator set via
/// [`from_validators`](PubkeyDirectory::from_validators).
#[derive(Debug, Clone)]
pub struct PubkeyDirectory {
    by_pubkey: HashMap<[u8; 32], ValidatorIndex>,
}

impl PubkeyDirectory {
    /// Builds a directory from `(public key, index)` pairs.
    pub fn new(entries: impl IntoIterator<Item = (PublicKey, ValidatorIndex)>) -> Self {
        let by_pubkey = entries
            .into_iter()
            .map(|(pk, id)| (*pk.as_bytes(), id))
            .collect();
        Self { by_pubkey }
    }

    /// Builds a directory mapping each validator's Ed25519 key to its index.
    #[must_use]
    pub fn from_validators(validators: &[ValidatorInfo]) -> Self {
        Self::new(validators.iter().map(|v| (v.pubkey, v.id)))
    }
}

impl PeerVerifier for PubkeyDirectory {
    fn resolve(&self, cert: &CertificateDer<'_>) -> Option<ValidatorIndex> {
        let pubkey = ed25519_pubkey_from_cert(cert)?;
        self.by_pubkey.get(&pubkey).copied()
    }
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

    /// Creates a QUIC network whose TLS identity is derived from `sk`: the
    /// validator's Ed25519 consensus key becomes the presented certificate.
    ///
    /// Convenience over [`self_signed_identity`] followed by [`new`](Self::new).
    ///
    /// # Errors
    ///
    /// Returns an error if certificate generation, socket binding, or TLS
    /// configuration fails.
    pub fn with_identity(
        port: u16,
        sk: &SecretKey,
        verifier: Arc<dyn PeerVerifier>,
    ) -> io::Result<Self> {
        let (cert, key) = self_signed_identity(sk)?;
        Self::new(port, cert, key, verifier)
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
    let validator = verifier.resolve(certs.first()?)?;
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

/// Builds a self-signed X.509 certificate whose subject public key is `sk`'s
/// Ed25519 identity key, together with that key in PKCS#8 form.
///
/// This is the credential a [`QuicNetwork`] presents during the handshake, so a
/// peer can bind the connection to the exact validator key that signs the node's
/// shreds and votes.
///
/// # Errors
///
/// Returns an error if certificate generation fails.
pub fn self_signed_identity(
    sk: &SecretKey,
) -> io::Result<(CertificateDer<'static>, PrivateKeyDer<'static>)> {
    let key_der = PrivatePkcs8KeyDer::from(ed25519_seed_to_pkcs8(sk.as_bytes()));
    let key_pair = rcgen::KeyPair::from_pkcs8_der_and_sign_algo(&key_der, &rcgen::PKCS_ED25519)
        .map_err(io::Error::other)?;
    // The subject name is irrelevant: peers are authenticated by the embedded
    // key, not by hostname, so any placeholder SAN works.
    let params =
        rcgen::CertificateParams::new(vec![SERVER_NAME.to_string()]).map_err(io::Error::other)?;
    let cert = params.self_signed(&key_pair).map_err(io::Error::other)?;
    Ok((cert.der().clone(), PrivateKeyDer::Pkcs8(key_der)))
}

/// Wraps a raw 32-byte Ed25519 seed in its PKCS#8 v1 DER encoding (RFC 8410).
fn ed25519_seed_to_pkcs8(seed: &[u8; 32]) -> Vec<u8> {
    // Fixed PKCS#8 v1 header for an Ed25519 `OneAsymmetricKey`: SEQUENCE {
    // version 0, AlgorithmIdentifier { 1.3.101.112 }, OCTET STRING { OCTET
    // STRING { <32-byte seed> } } }.
    const PREFIX: [u8; 16] = [
        0x30, 0x2e, 0x02, 0x01, 0x00, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x04, 0x22, 0x04,
        0x20,
    ];
    let mut der = Vec::with_capacity(PREFIX.len() + seed.len());
    der.extend_from_slice(&PREFIX);
    der.extend_from_slice(seed);
    der
}

/// Extracts the Ed25519 public key from a certificate's `SubjectPublicKeyInfo`.
///
/// Returns `None` if the certificate is malformed or its key is not Ed25519.
/// Safe on untrusted input: any parse failure yields `None` rather than a panic.
///
/// NOTE: the real SPKI must be parsed, not byte-searched — an adversary could
/// otherwise embed a victim's key bytes in an unrelated field while signing the
/// handshake with their own key, and be misattributed to the victim.
fn ed25519_pubkey_from_cert(cert: &CertificateDer<'_>) -> Option<[u8; 32]> {
    use x509_parser::prelude::FromDer;

    let (_, parsed) = x509_parser::certificate::X509Certificate::from_der(cert.as_ref()).ok()?;
    let spki = parsed.public_key();
    if spki.algorithm.algorithm != x509_parser::oid_registry::OID_SIG_ED25519 {
        return None;
    }
    spki.subject_public_key.data.as_ref().try_into().ok()
}

/// rustls plumbing: builds QUIC-compatible TLS configs whose peer verification
/// is delegated to a [`PeerVerifier`].
mod tls {
    use std::sync::Arc;

    use quinn::crypto::rustls::{QuicClientConfig, QuicServerConfig};
    use quinn::rustls::client::danger::{
        HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier,
    };
    use quinn::rustls::crypto::{
        CryptoProvider, verify_tls12_signature as verify_tls12,
        verify_tls13_signature as verify_tls13,
    };
    use quinn::rustls::pki_types::{CertificateDer, PrivateKeyDer, ServerName, UnixTime};
    use quinn::rustls::server::danger::{ClientCertVerified, ClientCertVerifier};
    use quinn::rustls::{
        self, CertificateError, DigitallySignedStruct, DistinguishedName, Error, SignatureScheme,
    };
    use quinn::{ClientConfig, ServerConfig};

    use super::PeerVerifier;

    /// ALPN protocol identifier negotiated during the TLS handshake.
    const ALPN: &[u8] = b"alpenglow/1";

    /// A fresh rustls crypto provider (ring backend, matching quinn's
    /// `rustls-ring` feature), avoiding reliance on a process-wide default.
    fn provider() -> Arc<CryptoProvider> {
        Arc::new(quinn::rustls::crypto::ring::default_provider())
    }

    /// The rejection returned when a certificate does not resolve to a validator.
    fn unknown_validator() -> Error {
        Error::InvalidCertificate(CertificateError::ApplicationVerificationFailure)
    }

    /// Builds the server-side config: presents `cert`/`key` and admits a client
    /// only if its certificate resolves to a validator (mutual TLS 1.3).
    ///
    /// # Errors
    ///
    /// Returns an error if the certificate/key is rejected or the resulting
    /// config is not QUIC-compatible.
    pub(super) fn server_config(
        cert: CertificateDer<'static>,
        key: PrivateKeyDer<'static>,
        verifier: Arc<dyn PeerVerifier>,
    ) -> std::io::Result<ServerConfig> {
        let provider = provider();
        let client_verifier = Arc::new(ValidatorClientVerifier {
            verifier,
            provider: provider.clone(),
        });
        let mut tls = rustls::ServerConfig::builder_with_provider(provider)
            .with_protocol_versions(&[&rustls::version::TLS13])
            .map_err(std::io::Error::other)?
            .with_client_cert_verifier(client_verifier)
            .with_single_cert(vec![cert], key)
            .map_err(std::io::Error::other)?;
        tls.alpn_protocols = vec![ALPN.to_vec()];
        let quic = QuicServerConfig::try_from(Arc::new(tls)).map_err(std::io::Error::other)?;
        Ok(ServerConfig::with_crypto(Arc::new(quic)))
    }

    /// Builds the client-side config: presents `cert`/`key` and admits a server
    /// only if its certificate resolves to a validator (mutual TLS 1.3).
    ///
    /// # Errors
    ///
    /// Returns an error if the certificate/key is rejected or the resulting
    /// config is not QUIC-compatible.
    pub(super) fn client_config(
        cert: CertificateDer<'static>,
        key: PrivateKeyDer<'static>,
        verifier: Arc<dyn PeerVerifier>,
    ) -> std::io::Result<ClientConfig> {
        let provider = provider();
        let server_verifier = Arc::new(ValidatorServerVerifier {
            verifier,
            provider: provider.clone(),
        });
        let mut tls = rustls::ClientConfig::builder_with_provider(provider)
            .with_protocol_versions(&[&rustls::version::TLS13])
            .map_err(std::io::Error::other)?
            .dangerous()
            .with_custom_certificate_verifier(server_verifier)
            .with_client_auth_cert(vec![cert], key)
            .map_err(std::io::Error::other)?;
        tls.alpn_protocols = vec![ALPN.to_vec()];
        let quic = QuicClientConfig::try_from(Arc::new(tls)).map_err(std::io::Error::other)?;
        Ok(ClientConfig::new(Arc::new(quic)))
    }

    /// Server-side verifier: admits a client iff its certificate resolves to a
    /// validator. Key possession is proven by the TLS `CertificateVerify`, whose
    /// signature is checked against the crypto provider's algorithms.
    #[derive(Debug)]
    struct ValidatorClientVerifier {
        verifier: Arc<dyn PeerVerifier>,
        provider: Arc<CryptoProvider>,
    }

    impl ClientCertVerifier for ValidatorClientVerifier {
        fn root_hint_subjects(&self) -> &[DistinguishedName] {
            &[]
        }

        fn verify_client_cert(
            &self,
            end_entity: &CertificateDer<'_>,
            _intermediates: &[CertificateDer<'_>],
            _now: UnixTime,
        ) -> Result<ClientCertVerified, Error> {
            self.verifier
                .resolve(end_entity)
                .map(|_| ClientCertVerified::assertion())
                .ok_or_else(unknown_validator)
        }

        fn verify_tls12_signature(
            &self,
            message: &[u8],
            cert: &CertificateDer<'_>,
            dss: &DigitallySignedStruct,
        ) -> Result<HandshakeSignatureValid, Error> {
            verify_tls12(
                message,
                cert,
                dss,
                &self.provider.signature_verification_algorithms,
            )
        }

        fn verify_tls13_signature(
            &self,
            message: &[u8],
            cert: &CertificateDer<'_>,
            dss: &DigitallySignedStruct,
        ) -> Result<HandshakeSignatureValid, Error> {
            verify_tls13(
                message,
                cert,
                dss,
                &self.provider.signature_verification_algorithms,
            )
        }

        fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
            self.provider
                .signature_verification_algorithms
                .supported_schemes()
        }
    }

    /// Client-side verifier: admits a server iff its certificate resolves to a
    /// validator. Same policy as [`ValidatorClientVerifier`].
    #[derive(Debug)]
    struct ValidatorServerVerifier {
        verifier: Arc<dyn PeerVerifier>,
        provider: Arc<CryptoProvider>,
    }

    impl ServerCertVerifier for ValidatorServerVerifier {
        fn verify_server_cert(
            &self,
            end_entity: &CertificateDer<'_>,
            _intermediates: &[CertificateDer<'_>],
            _server_name: &ServerName<'_>,
            _ocsp_response: &[u8],
            _now: UnixTime,
        ) -> Result<ServerCertVerified, Error> {
            self.verifier
                .resolve(end_entity)
                .map(|_| ServerCertVerified::assertion())
                .ok_or_else(unknown_validator)
        }

        fn verify_tls12_signature(
            &self,
            message: &[u8],
            cert: &CertificateDer<'_>,
            dss: &DigitallySignedStruct,
        ) -> Result<HandshakeSignatureValid, Error> {
            verify_tls12(
                message,
                cert,
                dss,
                &self.provider.signature_verification_algorithms,
            )
        }

        fn verify_tls13_signature(
            &self,
            message: &[u8],
            cert: &CertificateDer<'_>,
            dss: &DigitallySignedStruct,
        ) -> Result<HandshakeSignatureValid, Error> {
            verify_tls13(
                message,
                cert,
                dss,
                &self.provider.signature_verification_algorithms,
            )
        }

        fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
            self.provider
                .signature_verification_algorithms
                .supported_schemes()
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use tokio::time::timeout;

    use super::*;
    use crate::network::localhost_ip_sockaddr;
    use crate::test_utils::Ping;

    /// Builds a directory over `keys`, assigning validator indices in order.
    fn directory(keys: &[&SecretKey]) -> Arc<PubkeyDirectory> {
        Arc::new(PubkeyDirectory::new(
            keys.iter()
                .enumerate()
                .map(|(i, sk)| (sk.to_pk(), ValidatorIndex::new(i as u64))),
        ))
    }

    #[tokio::test]
    async fn authenticated_datagram_roundtrip() {
        let sk_a = SecretKey::new(&mut rand::rng());
        let sk_b = SecretKey::new(&mut rand::rng());
        let dir = directory(&[&sk_a, &sk_b]);

        let a: QuicNetwork<Ping, Ping> = QuicNetwork::with_identity(0, &sk_a, dir.clone()).unwrap();
        let b: QuicNetwork<Ping, Ping> = QuicNetwork::with_identity(0, &sk_b, dir).unwrap();
        let b_addr = localhost_ip_sockaddr(b.port());

        // `a` dials `b`; both prove their validator identity, then `a` sends.
        a.send(&Ping::default(), b_addr).await.unwrap();

        let (peer, _msg) = timeout(Duration::from_secs(5), b.receive_from())
            .await
            .expect("timed out waiting for datagram")
            .expect("receive failed");
        // the datagram is attributed to `a`'s validator index (0)
        assert_eq!(peer.validator(), Some(ValidatorIndex::new(0)));
    }

    #[tokio::test]
    async fn rejects_unknown_validator() {
        let sk_b = SecretKey::new(&mut rand::rng());
        let sk_outsider = SecretKey::new(&mut rand::rng());
        // the directory knows `b` but not the outsider
        let dir = directory(&[&sk_b]);

        let b: QuicNetwork<Ping, Ping> = QuicNetwork::with_identity(0, &sk_b, dir.clone()).unwrap();
        let outsider: QuicNetwork<Ping, Ping> =
            QuicNetwork::with_identity(0, &sk_outsider, dir).unwrap();
        let b_addr = localhost_ip_sockaddr(b.port());

        // The outsider's local dial may resolve — a TLS 1.3 client finishes before
        // the server validates its certificate — but `b` rejects the certificate
        // and never delivers an authenticated datagram, so the receive times out.
        let _ = outsider.send(&Ping::default(), b_addr).await;

        let received = timeout(Duration::from_secs(2), b.receive_from()).await;
        assert!(
            received.is_err(),
            "b must not deliver datagrams from an unknown validator"
        );
    }
}
