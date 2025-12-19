// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of a Merkle tree.
//!
//! It supports non-power-of-two leaf count by adding empty leaves.
//! That is, a tree with 3 leaves is equivalent to a tree with 4 leaves,
//! where the 4th leaf has the empty byte slice `&[]` as its data.
//!
//! The maximum height of trees supported is [`MAX_MERKLE_TREE_HEIGHT`].
//! Once constructed, the tree is immutable.
//!
//! Labels are used to reduce the impact of multiple attack vectors:
//! - multi-target attacks against this and other implementations
//! - rainbow tables / pre-calculation attacks
//! - ambiguity between leaf and inner nodes with unknown tree height

use std::marker::PhantomData;

use derive_more::{From, Into};
use hex_literal::hex;
use smallvec::SmallVec;
use static_assertions::const_assert;
use wincode::{SchemaRead, SchemaWrite};

use super::Hash;
use super::hash::hash_all;
use crate::shredder::TOTAL_SHREDS;
use crate::types::slice_index::MAX_SLICES_PER_BLOCK;

/// The hash of the genesis block.
pub const GENESIS_BLOCK_HASH: BlockHash = DoubleMerkleRoot(Hash([0; 32]));

/// Maximum height of Merkle trees currently supported.
pub const MAX_MERKLE_TREE_HEIGHT: usize = 32;
/// Maximum number of leaf nodes in the Merkle trees currently supported.
pub const MAX_MERKLE_TREE_LEAVES: usize = 1 << MAX_MERKLE_TREE_HEIGHT;
// need to be able to build Merkle tree for each slice
const_assert!(TOTAL_SHREDS <= MAX_MERKLE_TREE_LEAVES);
// need to be able to build double-Merkle tree for each block
const_assert!(MAX_SLICES_PER_BLOCK <= MAX_MERKLE_TREE_LEAVES);

const LEAF_LABEL: [u8; 32] = *b"ALPENGLOW-MERKLE-TREE  LEAF-NODE";
const LEFT_LABEL: [u8; 32] = *b"ALPENGLOW-MERKLE-TREE  LEFT-NODE";
const RIGHT_LABEL: [u8; 32] = *b"ALPENGLOW-MERKLE-TREE RIGHT-NODE";

/// Pre-calculated empty roots for up to `2 ^ MAX_MERKLE_TREE_HEIGHT` leaves.
///
/// These are calculated by running `cargo test -- empty_roots --no-capture`,
/// which is much faster than but equivalent to this straightforward snippet:
/// ```no_run
/// use alpenglow::crypto::hash::Hash;
/// use alpenglow::crypto::merkle::{MAX_MERKLE_TREE_HEIGHT, PlainMerkleTree};
///
/// for height in 0..MAX_MERKLE_TREE_HEIGHT {
///     let data = vec![vec![]; 1 << height];
///     let tree = PlainMerkleTree::new(&data);
///     println!("{}", hex::encode(tree.get_root()));
/// }
/// ```
///
/// Used for efficient check whether leaf is last in [`MerkleTree::check_proof_last`].
const EMPTY_ROOTS: [Hash; MAX_MERKLE_TREE_HEIGHT] = [
    Hash(hex!(
        "50c4672b7a309041b109458b1f3a11f82c225970975a95cd1025209301fcbcab"
    )),
    Hash(hex!(
        "2aa0cc78c82100f0fa3a26606a9794a928d5ddd0f5d381f93d6b0d64d065aa6f"
    )),
    Hash(hex!(
        "be22d038e2a34ff9386f4df7241c0a381ff433c98e36e2e0a59b3cfef7950c5b"
    )),
    Hash(hex!(
        "afc22402352574edbbfa7e3fd5221c7f1ab256c70ed826c8e2b8adc5b0b56ae9"
    )),
    Hash(hex!(
        "83831b4f0df87b978810491c31fd670c90e8e223e1a1f2876a96ab30c29161a4"
    )),
    Hash(hex!(
        "800e9e154844513cdbf5e11bec487c8953bcf2951d98eb5ef39cae18520d5e1b"
    )),
    Hash(hex!(
        "6c5328d45f1d420776a56188732b2ae0eba2956008148e4f0383eb8de65c65fe"
    )),
    Hash(hex!(
        "c356e3d71c9aae22fb8e449ad2d37b795b9861bb8fbb028c2378c86eff2e0a26"
    )),
    Hash(hex!(
        "89c79a35bdbb8aa17e08560fdbc0bbc3f2fc6ba882deedf81a3f37c4534e9e3d"
    )),
    Hash(hex!(
        "e5fefbb76548773dd0ba0765286fe98d1b6560bafd1abc071120380f4fb0bb78"
    )),
    Hash(hex!(
        "24a72454e312eddaee4f4504e04e309152f27dd9848bb5c648f5f6a0aa960cb1"
    )),
    Hash(hex!(
        "1be1a1ccce5c9dee569c7560033f41414c10792939408d857f35cb2c4273877d"
    )),
    Hash(hex!(
        "b43f0ce6212391b7c57b2452a6d989db222ae6f274d8cdfafc28afd98d267e23"
    )),
    Hash(hex!(
        "3f346c4f375fe9a9a9d41ad270bd36d69409e2c7d8b4c38653b6d7d225a6add5"
    )),
    Hash(hex!(
        "3c4120e345597ad037337dd72d2c536553e2b52242f4ef81ce8def38d17b38af"
    )),
    Hash(hex!(
        "4396524427a665c659fea115ce68d3357ce1d6a04ca5b8eeb69d76e439ea2247"
    )),
    Hash(hex!(
        "68eb4a1c412f67ef86dadaa6c5b6cf2ba5e7bd266645b69bb12a1d10704487f7"
    )),
    Hash(hex!(
        "75271d1c9e8b79fdeaceb051cfd29ed03350e4808b262e3a750277c82a2a5206"
    )),
    Hash(hex!(
        "b99c05ba6039ddcb754abcf9e66aeb529348e708220569fe20cc4d587ddbd267"
    )),
    Hash(hex!(
        "a0f8ea088f640460978534c9821ae114231e0730bff2c361b64a5824a3237341"
    )),
    Hash(hex!(
        "b50f9fa20d9df525a29ccfe4cbe9b014142275e7e5ac9ef81a6c20112774418c"
    )),
    Hash(hex!(
        "b48a3973c4e0c5bad395ecd1c0cd430adc9680c7fd574460bf21c45f74840662"
    )),
    Hash(hex!(
        "826bfb27619fbf799f6000e4a3acdec264a13661e9c730e265c1c74c63501cb3"
    )),
    Hash(hex!(
        "720d56bf703cd7677805d33e73d2e7cb6104c932b62458ac3ae2f9d7469a1f38"
    )),
    Hash(hex!(
        "ab2960c67fdd892b5eb1e63ac0c182c8d174671fd0f8065363895b5a3f7f0a88"
    )),
    Hash(hex!(
        "ab7f4126b993ca5037a84190933bb8b97b9427a977d6872ca0b5d61470ea1834"
    )),
    Hash(hex!(
        "dfaae89b54a08d497b2e8251de039fb38a7137b802d2d6c2554540c7b027721a"
    )),
    Hash(hex!(
        "9451a516e349a64cd75fde5558bc92d3f359d3d49b560d2414b7eaa1e6889b1e"
    )),
    Hash(hex!(
        "1c78453e429f9dbeaa70097b76abe42ad3da19a2ec5cda345aa77d713b930145"
    )),
    Hash(hex!(
        "ee4878f4417f8dea52e54aaad49962a9fab5b746e54d6c49a5125e41e3ed6511"
    )),
    Hash(hex!(
        "0cca41b299cd9be76a4b810fcbfff766e3f93ae2d8c7d761c0af2b524af97b56"
    )),
    Hash(hex!(
        "33ebfb34d3aa119cb665d564acdd77b318dc86aa6a97744edb3bc03e97d776ca"
    )),
];

/// Marker trait for the leaf nodes of a Merkle tree.
pub trait MerkleLeaf: AsRef<[u8]> {}

/// Trait for the root of a Merkle tree.
pub trait MerkleRoot: From<Hash> {
    fn as_hash(&self) -> &Hash;
}

/// Marker trait for the proof of a Merkle tree.
pub trait MerkleProof: AsRef<[Hash]> + From<Vec<Hash>> {}

impl<T> MerkleLeaf for T where T: AsRef<[u8]> {}
impl MerkleRoot for Hash {
    fn as_hash(&self) -> &Hash {
        self
    }
}
impl MerkleProof for Vec<Hash> {}

#[repr(transparent)]
#[derive(
    Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, From, Into, SchemaRead, SchemaWrite,
)]
pub struct SliceRoot(Hash);
impl MerkleRoot for SliceRoot {
    fn as_hash(&self) -> &Hash {
        &self.0
    }
}

impl AsRef<[u8]> for SliceRoot {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

#[repr(transparent)]
#[derive(Clone, Debug, PartialEq, Eq, From, Into, SchemaRead, SchemaWrite)]
pub struct SliceProof(Vec<Hash>);
impl MerkleProof for SliceProof {}

impl AsRef<[Hash]> for SliceProof {
    fn as_ref(&self) -> &[Hash] {
        self.0.as_ref()
    }
}

#[repr(transparent)]
#[derive(
    Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, From, Into, SchemaRead, SchemaWrite,
)]
pub struct DoubleMerkleRoot(Hash);
impl MerkleRoot for DoubleMerkleRoot {
    fn as_hash(&self) -> &Hash {
        &self.0
    }
}

#[repr(transparent)]
#[derive(Clone, Debug, PartialEq, Eq, From, Into, SchemaRead, SchemaWrite)]
pub struct DoubleMerkleProof(Vec<Hash>);
impl MerkleProof for DoubleMerkleProof {}
pub type BlockHash = DoubleMerkleRoot;

impl AsRef<[Hash]> for DoubleMerkleProof {
    fn as_ref(&self) -> &[Hash] {
        self.0.as_ref()
    }
}

/// A plain Merkle tree over arbitrary bytes.
///
/// Usually, you want the additional type-safety of not using these basic types.
/// For this implement [`MerkleLeaf`], [`MerkleRoot`] and [`MerkleProof`] on your own types.
pub type PlainMerkleTree = MerkleTree<Vec<u8>, Hash, Vec<Hash>>;

/// Per-slice Merkle tree for use in Rotor.
///
/// The leaves of this tree are shreds within a single slice of a block.
/// The root of this tree is signed by the leader and included in each shred, together with a proof.
pub type SliceMerkleTree = MerkleTree<Vec<u8>, SliceRoot, SliceProof>;

/// Alpenglow's double-Merkle tree.
///
/// The leaves of this tree are roots of per-slice Merkle trees.
/// The root of this tree represents the block hash.
pub type DoubleMerkleTree = MerkleTree<SliceRoot, DoubleMerkleRoot, DoubleMerkleProof>;

/// Implementation of a Merkle tree.
pub struct MerkleTree<Leaf: MerkleLeaf, Root: MerkleRoot, Proof: MerkleProof> {
    /// All hashes in the tree, leaf hashes and inner nodes.
    nodes: Vec<Hash>,
    /// For each level, has the offset in `nodes` and the number of hashes on that level.
    levels: SmallVec<[(u32, u32); MAX_MERKLE_TREE_HEIGHT]>,
    /// Marker for the type of the tree.
    _type: PhantomData<(Leaf, Root, Proof)>,
}

impl<Leaf: MerkleLeaf, Root: MerkleRoot, Proof: MerkleProof> MerkleTree<Leaf, Root, Proof> {
    /// Creates a new Merkle tree from the given data for each leaf.
    ///
    /// This will always create a perfect binary tree (filling with empty leaves as necessary).
    /// If you want to create a tree with more than half of the leaves empty,
    /// you have to explicitly pass in empty leaves as part of `data`.
    pub fn new<'a>(data: impl IntoIterator<Item = &'a Leaf>) -> Self
    where
        Leaf: 'a,
    {
        // calculate leaf hashes
        let mut nodes = data
            .into_iter()
            .map(|leaf| Self::hash_leaf(leaf))
            .collect::<Vec<Hash>>();
        assert!(!nodes.is_empty());

        // reserve enough space for inner nodes
        let mut num_inner_nodes = 1;
        for i in 1..=nodes.len().ilog2() {
            num_inner_nodes += nodes.len().div_ceil(1 << i);
        }
        nodes.reserve(num_inner_nodes);

        // prepare levels index with correct size
        let mut levels = SmallVec::new();
        levels.push((0, nodes.len().try_into().expect("too many leaves")));

        // calculate inner nodes
        let mut left = 0;
        let mut right = nodes.len();
        let mut len = right - left;
        let mut h = 0;
        while len > 1 {
            for i in (left..right).step_by(2) {
                if i == right {
                    break;
                } else if i + 1 == right {
                    let inner_node = Self::hash_pair(&nodes[i], &EMPTY_ROOTS[h]);
                    nodes.push(inner_node);
                    break;
                }
                let inner_node = Self::hash_pair(&nodes[i], &nodes[i + 1]);
                nodes.push(inner_node);
            }

            len = len.div_ceil(2);
            left = right;
            right = left + len;
            h += 1;
            levels.push((left as u32, len as u32));
        }

        Self {
            nodes,
            levels,
            _type: PhantomData,
        }
    }

    /// Gives the root hash of the tree.
    #[must_use]
    pub fn get_root(&self) -> Root {
        let root_hash = self.nodes.last().expect("empty tree").clone();
        root_hash.into()
    }

    /// Gives the height of the tree.
    pub fn height(&self) -> usize {
        self.levels.len() - 1
    }

    /// Generates a proof of membership for the element at the given `index`.
    ///
    /// The proof is the Merkle path from the leaf to the root.
    #[must_use]
    pub fn create_proof(&self, index: usize) -> Proof {
        assert!(index < 1 << self.height());
        assert!(index < self.levels[0].1 as usize);

        let mut proof = Vec::with_capacity(self.height());
        let mut i = index;

        for (h, (offset, len)) in self.levels.iter().enumerate().take(self.height()) {
            if i ^ 1 >= *len as usize {
                proof.push(EMPTY_ROOTS[h].clone());
            } else {
                proof.push(self.nodes[*offset as usize + (i ^ 1)].clone());
            }
            i /= 2;
        }
        proof.into()
    }

    /// Checks a Merkle path against a leaf's data.
    ///
    /// Returns `true` iff `proof` is a valid Merkle path for a leaf containing
    /// `data` at the given `index` in the tree corresponding to the given `root`.
    #[must_use]
    pub fn check_proof(data: &Leaf, index: usize, root: &Root, proof: &Proof) -> bool {
        let hash = Self::hash_leaf(data);
        Self::check_hash_proof(hash, index, root, proof)
    }

    /// Checks a Merkle path against a leaf hash.
    ///
    /// Returns `true` iff `proof` is a valid Merkle path for a leaf that hashes
    /// to the given `hash` at the given `index` in the tree corresponding to the given `root`.
    #[must_use]
    fn check_hash_proof(hash: Hash, index: usize, root: &Root, proof: &Proof) -> bool {
        let mut i = index;
        let mut node = hash;
        for h in proof.as_ref() {
            node = match i % 2 {
                0 => Self::hash_pair(&node, h),
                _ => Self::hash_pair(h, &node),
            };
            i /= 2;
        }
        node == *root.as_hash()
    }

    /// Checks a Merkle path proves the given leaf's data is last in the tree.
    ///
    /// Returns `true` iff the Merkle proof is valid and `index` is the last leaf in the tree.
    #[must_use]
    pub fn check_proof_last(leaf: &Leaf, index: usize, root: &Root, proof: &Proof) -> bool {
        let hash = Self::hash_leaf(leaf);
        Self::check_hash_proof_last(hash, index, root, proof)
    }

    /// Checks a Merkle path proves the given leaf hash is last in the tree.
    ///
    /// Returns `true` iff the Merkle proof is valid and `index` is the last leaf in the tree.
    #[must_use]
    fn check_hash_proof_last(hash: Hash, index: usize, root: &Root, proof: &Proof) -> bool {
        assert!(proof.as_ref().len() <= MAX_MERKLE_TREE_HEIGHT);
        let mut i = index;
        let mut node = hash;
        for (height, h) in proof.as_ref().iter().enumerate() {
            node = match i % 2 {
                0 => Self::hash_pair(&node, &EMPTY_ROOTS[height]),
                _ => Self::hash_pair(h, &node),
            };
            i /= 2;
        }
        node == *root.as_hash()
    }

    /// Hashes some leaf data with a label into a leaf node.
    ///
    /// The label prevents the possibility to claim an intermediate node was a leaf.
    /// It also makes the Merkle tree more robust against pre-calculation attacks.
    fn hash_leaf(leaf: &Leaf) -> Hash {
        let data: &[u8] = leaf.as_ref();
        hash_all(&[&LEAF_LABEL, data])
    }

    /// Hashes a pair of child hashes with labels into a parent (non-leaf) node.
    ///
    /// The labels prevent the possibility to claim an intermediate node was a leaf.
    /// They also make the Merkle tree more robust against pre-calculation attacks.
    fn hash_pair(left: &Hash, right: &Hash) -> Hash {
        hash_all(&[&LEFT_LABEL, left.as_ref(), &RIGHT_LABEL, right.as_ref()])
    }
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;

    use super::*;

    #[test]
    fn basic() {
        let data = [b"hello".to_vec(), b"world".to_vec()];
        let tree = PlainMerkleTree::new(&data);
        assert_eq!(tree.nodes.len(), 3);
    }

    #[test]
    fn two_leaves() {
        let data = [b"hello".to_vec(), b"world".to_vec()];
        let tree = PlainMerkleTree::new(&data);

        // calculate expected root hash manually
        let leaf1 = PlainMerkleTree::hash_leaf(&data[0]);
        let leaf2 = PlainMerkleTree::hash_leaf(&data[1]);
        let expected_root = PlainMerkleTree::hash_pair(&leaf1, &leaf2);

        assert_eq!(tree.get_root(), expected_root);
    }

    #[test]
    fn empty_trees() {
        // one empty leaf
        let data = [vec![]];
        let tree1 = PlainMerkleTree::new(&data);

        // two empty leaves
        let data = [vec![], vec![]];
        let tree2 = PlainMerkleTree::new(&data);

        // these should have different roots
        assert_ne!(tree1.get_root(), tree2.get_root());
    }

    #[test]
    fn proofs() {
        let data = [
            b"hello".to_vec(),
            b"world".to_vec(),
            b"data".to_vec(),
            b"test".to_vec(),
        ];
        let tree = PlainMerkleTree::new(&data);
        let root = tree.get_root();

        // proof and verify all leaves
        let proof = tree.create_proof(0);
        assert!(PlainMerkleTree::check_proof(&data[0], 0, &root, &proof));
        let proof = tree.create_proof(1);
        assert!(PlainMerkleTree::check_proof(&data[1], 1, &root, &proof));
        let proof = tree.create_proof(2);
        assert!(PlainMerkleTree::check_proof(&data[2], 2, &root, &proof));
        let proof = tree.create_proof(3);
        assert!(PlainMerkleTree::check_proof(&data[3], 3, &root, &proof));
    }

    #[test]
    fn three_leaves() {
        let data1 = [b"a".to_vec(), b"b".to_vec(), b"c".to_vec()];
        let tree1 = PlainMerkleTree::new(&data1);

        let data2 = [b"a".to_vec(), b"b".to_vec(), b"c".to_vec(), vec![]];
        let tree2 = PlainMerkleTree::new(&data2);

        // missing leaves should be equivalent to empty leaves
        assert_eq!(tree1.get_root(), tree2.get_root());
    }

    #[test]
    fn non_power_of_two() {
        let data1 = vec![b"hello".to_vec(); 33];
        let tree1 = PlainMerkleTree::new(&data1);

        let mut data2 = vec![b"hello".to_vec(); 33];
        let empty_slice = vec![];
        data2.extend_from_slice(vec![empty_slice; 31].as_slice());
        let tree2 = PlainMerkleTree::new(data2.as_slice());

        // missing leaves should be equivalent to empty leaves
        assert_eq!(tree1.get_root(), tree2.get_root());
    }

    #[test]
    fn proof_last() {
        let data = vec![b"hello".to_vec(); 33];
        let tree = PlainMerkleTree::new(&data);
        let root = tree.get_root();

        let proof = tree.create_proof(31);
        assert!(!PlainMerkleTree::check_proof_last(
            &data[31], 31, &root, &proof
        ));

        let proof = tree.create_proof(32);
        assert!(PlainMerkleTree::check_proof_last(
            &data[32], 32, &root, &proof
        ));
    }

    #[test]
    fn fuzzing() {
        const ITERATIONS: u64 = 10_000;
        const MAX_NUM_LEAVES: usize = 64;
        const MAX_LEAF_DATA_LEN: usize = 64;
        const QUERIES_PER_TREE: usize = 10;

        let mut rng = rand::rng();
        for _ in 0..ITERATIONS {
            let num_data = rng.random_range(1..=MAX_NUM_LEAVES);
            let mut data = Vec::with_capacity(num_data);
            for _ in 0..num_data {
                let leaf_data_len = rng.random_range(0..=MAX_LEAF_DATA_LEN);
                let mut leaf_data = vec![0; leaf_data_len];
                rng.fill_bytes(&mut leaf_data);
                data.push(leaf_data);
            }

            let tree = PlainMerkleTree::new(data.iter());
            let root = tree.get_root();
            for _ in 0..QUERIES_PER_TREE {
                let index = rng.random_range(0..num_data);
                let proof = tree.create_proof(index);
                let leaf = &data[index];
                assert!(PlainMerkleTree::check_proof(leaf, index, &root, &proof));
                if index == num_data - 1 {
                    assert!(PlainMerkleTree::check_proof_last(
                        leaf, index, &root, &proof
                    ));
                }
            }
        }
    }

    // NOTE: This is used for calculating `EMPTY_ROOTS`.
    #[test]
    fn empty_roots() {
        for (height, empty_root) in EMPTY_ROOTS.iter().enumerate() {
            let mut node = PlainMerkleTree::hash_leaf(&vec![]);
            for _ in 0..height {
                node = PlainMerkleTree::hash_pair(&node, &node);
            }
            assert_eq!(node, *empty_root);
            println!("{}", hex::encode(node));
        }
    }
}
