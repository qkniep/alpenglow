#[cfg(test)]
use std::sync::Arc;

#[cfg(test)]
use crate::{
    ValidatorId, ValidatorInfo,
    all2all::TrivialAll2All,
    consensus::EpochInfo,
    crypto::{aggsig::SecretKey, signature},
    network::SimulatedNetwork,
    network::simulated::SimulatedNetworkCore,
};

#[cfg(test)]
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

#[cfg(test)]
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
