use std::collections::btree_map::Entry;

use crate::{
    crypto::{Hash, MerkleTree, signature::PublicKey},
    shredder::Shred,
    types::SliceIndex,
};

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct ValidatedShred(Shred);

impl ValidatedShred {
    pub fn new(shred: Shred, merkle_root: Entry<SliceIndex, Hash>, pk: &PublicKey) -> Option<Self> {
        if !MerkleTree::check_proof(
            &shred.payload().data,
            shred.payload().index_in_slice,
            shred.merkle_root,
            &shred.merkle_path,
        ) {
            return None;
        }
        match merkle_root {
            Entry::Occupied(entry) => (entry.get() == &shred.merkle_root).then_some(Self(shred)),
            Entry::Vacant(entry) => {
                if shred.merkle_root_sig.verify(&shred.merkle_root, pk) {
                    entry.insert(shred.merkle_root);
                    Some(Self(shred))
                } else {
                    None
                }
            }
        }
    }

    pub fn to_shred(&self) -> &Shred {
        &self.0
    }

    pub fn into_shred(self) -> Shred {
        self.0
    }
}
