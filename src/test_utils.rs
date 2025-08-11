use std::sync::Arc;

use crate::{
    Slot, ValidatorId, ValidatorInfo, VotorEvent,
    all2all::TrivialAll2All,
    consensus::EpochInfo,
    crypto::{Hash, aggsig::SecretKey, signature},
    network::{SimulatedNetwork, simulated::SimulatedNetworkCore},
    shredder::MAX_DATA_PER_SLICE,
    slice::{Slice, SliceHeader, create_random_slice_payload},
};

pub fn generate_validators(num_validators: u64) -> (Vec<SecretKey>, Arc<EpochInfo>) {
    let mut rng = rand::rng();
    let mut sks = Vec::new();
    let mut voting_sks = Vec::new();
    let mut validators = Vec::new();
    for i in 0..num_validators {
        sks.push(signature::SecretKey::new(&mut rng));
        voting_sks.push(SecretKey::new(&mut rng));
        validators.push(ValidatorInfo {
            id: i,
            stake: 1,
            pubkey: sks[i as usize].to_pk(),
            voting_pubkey: voting_sks[i as usize].to_pk(),
            all2all_address: String::new(),
            disseminator_address: String::new(),
            repair_address: String::new(),
        });
    }
    let epoch_info = Arc::new(EpochInfo::new(0, validators));
    (voting_sks, epoch_info)
}

pub async fn generate_all2all_instances(
    mut validators: Vec<ValidatorInfo>,
) -> Vec<TrivialAll2All<SimulatedNetwork>> {
    let core = Arc::new(
        SimulatedNetworkCore::default()
            .with_jitter(0.0)
            .with_packet_loss(0.0),
    );
    for (i, val) in validators.iter_mut().enumerate() {
        val.all2all_address = i.to_string();
    }
    let mut all2all = Vec::new();
    for i in 0..validators.len() {
        let network = core.join_unlimited(i as ValidatorId).await;
        all2all.push(TrivialAll2All::new(validators.clone(), network));
    }
    all2all
}

pub fn create_random_block(slot: Slot, num_slices: usize) -> Vec<Slice> {
    let parent_slot = Slot::new(0);
    assert_ne!(slot, parent_slot);
    let mut slices = Vec::new();
    for slice_index in 0..num_slices {
        let parent = if slice_index == 0 {
            Some((parent_slot, Hash::default()))
        } else {
            None
        };
        let payload = create_random_slice_payload(parent, MAX_DATA_PER_SLICE);
        let header = SliceHeader {
            slot,
            slice_index,
            is_last: slice_index == num_slices - 1,
        };
        slices.push(Slice::from_parts(header, payload, None));
    }
    slices
}

pub fn assert_votor_events_match(ev0: VotorEvent, ev1: VotorEvent) {
    match (ev0, ev1) {
        (
            VotorEvent::ParentReady {
                slot: s0,
                parent_slot: ps0,
                parent_hash: ph0,
            },
            VotorEvent::ParentReady {
                slot: s1,
                parent_slot: ps1,
                parent_hash: ph1,
            },
        ) => {
            assert_eq!(s0, s1);
            assert_eq!(ps0, ps1);
            assert_eq!(ph0, ph1);
        }
        (VotorEvent::CertCreated(c0), VotorEvent::CertCreated(c1)) => assert_eq!(c0, c1),
        (VotorEvent::Standstill(s0, c0, v0), VotorEvent::Standstill(s1, c1, v1)) => {
            assert_eq!(s0, s1);
            assert_eq!(c0, c1);
            assert_eq!(v0, v1);
        }
        (VotorEvent::SafeToNotar(s0, h0), VotorEvent::SafeToNotar(s1, h1)) => {
            assert_eq!(s0, s1);
            assert_eq!(h0, h1);
        }
        (
            VotorEvent::Block {
                slot: s0,
                block_info: b0,
            },
            VotorEvent::Block {
                slot: s1,
                block_info: b1,
            },
        ) => {
            assert_eq!(s0, s1);
            assert_eq!(b0, b1);
        }

        (VotorEvent::Timeout(s0), VotorEvent::Timeout(s1))
        | (VotorEvent::TimeoutCrashedLeader(s0), VotorEvent::TimeoutCrashedLeader(s1))
        | (VotorEvent::SafeToSkip(s0), VotorEvent::SafeToSkip(s1)) => assert_eq!(s0, s1),
        (VotorEvent::FirstShred(s0), VotorEvent::FirstShred(s1)) => assert_eq!(s0, s1),

        (ev0, ev1) => {
            panic!("{ev0:?} does not match {ev1:?}");
        }
    }
}
