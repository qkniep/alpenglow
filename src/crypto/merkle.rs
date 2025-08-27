// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of a Merkle tree.
//!
//! It supports non-power-of-two leaf count by adding empty leaves.
//! That is, a tree with 3 leaves is equivalent to a tree with 4 leaves,
//! where the 4th leaf has the empty byte slice `&[]` as its data.
//!
//! Labels are used to reduce the impact of multiple attack vectors:
//! - multi-target attacks against this and other implementations
//! - rainbow tables / pre-calculation attacks
//! - ambiguity between leaf and inner nodes with unknown tree height

use hex_literal::hex;

use super::Hash;
use super::hash::hash_all;

const LEAF_LABEL: [u8; 32] = *b"ALPENGLOW-MERKLE-TREE  LEAF-NODE";
const LEFT_LABEL: [u8; 32] = *b"ALPENGLOW-MERKLE-TREE  LEFT-NODE";
const RIGHT_LABEL: [u8; 32] = *b"ALPENGLOW-MERKLE-TREE RIGHT-NODE";

const EMPTY_ROOTS: [Hash; 24] = [
    hex!("50c4672b7a309041b109458b1f3a11f82c225970975a95cd1025209301fcbcab"),
    hex!("2aa0cc78c82100f0fa3a26606a9794a928d5ddd0f5d381f93d6b0d64d065aa6f"),
    hex!("be22d038e2a34ff9386f4df7241c0a381ff433c98e36e2e0a59b3cfef7950c5b"),
    hex!("afc22402352574edbbfa7e3fd5221c7f1ab256c70ed826c8e2b8adc5b0b56ae9"),
    hex!("83831b4f0df87b978810491c31fd670c90e8e223e1a1f2876a96ab30c29161a4"),
    hex!("800e9e154844513cdbf5e11bec487c8953bcf2951d98eb5ef39cae18520d5e1b"),
    hex!("6c5328d45f1d420776a56188732b2ae0eba2956008148e4f0383eb8de65c65fe"),
    hex!("c356e3d71c9aae22fb8e449ad2d37b795b9861bb8fbb028c2378c86eff2e0a26"),
    hex!("89c79a35bdbb8aa17e08560fdbc0bbc3f2fc6ba882deedf81a3f37c4534e9e3d"),
    hex!("e5fefbb76548773dd0ba0765286fe98d1b6560bafd1abc071120380f4fb0bb78"),
    hex!("24a72454e312eddaee4f4504e04e309152f27dd9848bb5c648f5f6a0aa960cb1"),
    hex!("1be1a1ccce5c9dee569c7560033f41414c10792939408d857f35cb2c4273877d"),
    hex!("b43f0ce6212391b7c57b2452a6d989db222ae6f274d8cdfafc28afd98d267e23"),
    hex!("3f346c4f375fe9a9a9d41ad270bd36d69409e2c7d8b4c38653b6d7d225a6add5"),
    hex!("3c4120e345597ad037337dd72d2c536553e2b52242f4ef81ce8def38d17b38af"),
    hex!("4396524427a665c659fea115ce68d3357ce1d6a04ca5b8eeb69d76e439ea2247"),
    hex!("68eb4a1c412f67ef86dadaa6c5b6cf2ba5e7bd266645b69bb12a1d10704487f7"),
    hex!("75271d1c9e8b79fdeaceb051cfd29ed03350e4808b262e3a750277c82a2a5206"),
    hex!("b99c05ba6039ddcb754abcf9e66aeb529348e708220569fe20cc4d587ddbd267"),
    hex!("a0f8ea088f640460978534c9821ae114231e0730bff2c361b64a5824a3237341"),
    hex!("b50f9fa20d9df525a29ccfe4cbe9b014142275e7e5ac9ef81a6c20112774418c"),
    hex!("b48a3973c4e0c5bad395ecd1c0cd430adc9680c7fd574460bf21c45f74840662"),
    hex!("826bfb27619fbf799f6000e4a3acdec264a13661e9c730e265c1c74c63501cb3"),
    hex!("720d56bf703cd7677805d33e73d2e7cb6104c932b62458ac3ae2f9d7469a1f38"),
];

/// Implementation of a Merkle tree.
pub struct MerkleTree {
    nodes: Vec<Hash>,
    height: usize,
}

impl MerkleTree {
    /// Creates a new Merkle tree from the given data for each leaf.
    pub fn new(data: &[impl AsRef<[u8]>]) -> Self {
        Self::new_from_iter(data.iter().map(|leaf| leaf.as_ref()))
    }

    /// Creates a new Merkle tree from the given data for each leaf.
    pub fn new_from_iter<'a>(data: impl IntoIterator<Item = &'a [u8]>) -> Self {
        let mut nodes = Vec::new();
        let mut height = 0;

        // calculate leaf hashes
        for leaf in data {
            let leaf_hash = hash_leaf(leaf);
            nodes.push(leaf_hash);
        }

        // PERF: precompute these
        let empty_leaf_hash = hash_leaf(&[]);
        while !nodes.len().is_power_of_two() {
            nodes.push(empty_leaf_hash);
        }

        // calculate inner nodes
        let mut left = 0;
        let mut right = nodes.len();
        let mut len = right - left;
        while len > 1 {
            for i in (left..right).step_by(2) {
                let inner_node = hash_pair(nodes[i], nodes[i + 1]);
                nodes.push(inner_node);
            }

            len /= 2;
            left = right;
            right = left + len;
            height += 1;
        }

        Self { nodes, height }
    }

    /// Gives the root hash of the tree.
    #[must_use]
    pub fn get_root(&self) -> Hash {
        *self.nodes.last().expect("empty tree")
    }

    /// Generates a proof of membership for the element at the given `index`.
    /// The proof is the Merkle path from the leaf to the root.
    #[must_use]
    pub fn create_proof(&self, index: usize) -> Vec<Hash> {
        // TODO: handle out-of-bounds index
        let mut proof = Vec::new();
        let mut i = index;
        let mut left = 0;
        let mut right = 1 << self.height;
        let mut len = right - left;
        while len > 1 {
            proof.push(self.nodes[left + (i ^ 1)]);
            len /= 2;
            left = right;
            right = left + len;
            i /= 2;
        }
        proof
    }

    /// Checks a Merkle path against a leaf's data.
    ///
    /// Returns `true` iff `proof` is a valid Merkle path for a leaf containing
    /// `data` at the given `index` in the tree corresponding to the given `root`.
    #[must_use]
    pub fn check_proof(data: &[u8], index: usize, root: Hash, proof: &[Hash]) -> bool {
        let hash = hash_leaf(data);
        Self::check_hash_proof(hash, index, root, proof)
    }

    /// Checks a Merkle path against a leaf hash.
    ///
    /// Returns `true` iff `proof` is a valid Merkle path for a leaf that hashes
    /// to the given `hash` at the given `index` in the tree corresponding to
    /// the given `root`.
    #[must_use]
    pub fn check_hash_proof(hash: Hash, index: usize, root: Hash, proof: &[Hash]) -> bool {
        let mut i = index;
        let mut node = hash;
        for h in proof {
            node = match i % 2 {
                0 => hash_pair(node, *h),
                _ => hash_pair(*h, node),
            };
            i /= 2;
        }
        node == root
    }

    /// Checks a Merkle path proves the given leaf's data is last in the tree.
    ///
    /// Returns `true` iff the Merkle proof is valid and `index` is the last leaf in the tree.
    #[must_use]
    pub fn check_proof_last(data: &[u8], index: usize, root: Hash, proof: &[Hash]) -> bool {
        let hash = hash_leaf(data);
        Self::check_hash_proof_last(hash, index, root, proof)
    }

    /// Checks a Merkle path proves the given leaf hash is last in the tree.
    ///
    /// Returns `true` iff the Merkle proof is valid and `index` is the last leaf in the tree.
    #[must_use]
    pub fn check_hash_proof_last(hash: Hash, index: usize, root: Hash, proof: &[Hash]) -> bool {
        assert!(proof.len() <= EMPTY_ROOTS.len());
        let mut i = index;
        let mut node = hash;
        for (height, h) in proof.iter().enumerate() {
            node = match i % 2 {
                0 => hash_pair(node, EMPTY_ROOTS[height]),
                _ => hash_pair(*h, node),
            };
            i /= 2;
        }
        node == root
    }
}

/// Hash a leaf data with a label.
///
/// The label prevents the possibility to claim an intermediate node was a leaf.
/// It also makes the Merkle tree more robust against pre-calculation attacks.
fn hash_leaf(data: &[u8]) -> Hash {
    hash_all(&[&LEAF_LABEL[..], data])
}

/// Hashes a pair of child hashes into a parent non-leaf node with labels.
///
/// The labels prevent the possibility to claim an intermediate node was a leaf.
/// They also make the Merkle tree more robust against pre-calculation attacks.
fn hash_pair(left: Hash, right: Hash) -> Hash {
    hash_all(&[&LEFT_LABEL[..], &left, &RIGHT_LABEL[..], &right])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let data = [b"hello", b"world"];
        let tree = MerkleTree::new(&data);
        assert_eq!(tree.nodes.len(), 3);
    }

    #[test]
    fn two_leaves() {
        let data = [b"hello", b"world"];
        let tree = MerkleTree::new(&data);

        // calculate expected root hash manually
        let leaf1 = hash_leaf(b"hello");
        let leaf2 = hash_leaf(b"world");
        let expected_root = hash_pair(leaf1, leaf2);

        assert_eq!(tree.get_root(), expected_root);
    }

    #[test]
    fn zero_leaves() {
        let data = [b""];
        let tree = MerkleTree::new(&data);

        // check root hash of zero-length leaf
        let expected_root = hash_leaf(b"");
        assert_eq!(tree.get_root(), expected_root);
    }

    #[test]
    fn proofs() {
        let data = [&b"hello"[..], &b"world"[..], &b"data"[..], &b"test"[..]];
        let tree = MerkleTree::new(&data);
        let root = tree.get_root();

        // proof and verify all leaves
        let proof = tree.create_proof(0);
        assert!(MerkleTree::check_proof(b"hello", 0, root, &proof));
        let proof = tree.create_proof(1);
        assert!(MerkleTree::check_proof(b"world", 1, root, &proof));
        let proof = tree.create_proof(2);
        assert!(MerkleTree::check_proof(b"data", 2, root, &proof));
        let proof = tree.create_proof(3);
        assert!(MerkleTree::check_proof(b"test", 3, root, &proof));
    }

    #[test]
    fn three_leaves() {
        let data = [b"a", b"b", b"c"];
        let tree = MerkleTree::new(&data);

        // verify proper handling of non-power-of-two leaves by checking node count
        assert_eq!(tree.nodes.len(), 4 + 2 + 1);
    }

    #[test]
    fn non_power_of_two() {
        let data1 = vec![b"hello"; 33];
        let tree1 = MerkleTree::new(&data1);

        let mut data2 = vec![&b"hello"[..]; 33];
        let empty_slice: &[u8] = &[];
        data2.extend_from_slice(vec![empty_slice; 31].as_slice());
        let tree2 = MerkleTree::new(&data2);

        // missing leaves should be equivalent to empty leaves
        assert_eq!(tree1.get_root(), tree2.get_root());
    }

    #[test]
    fn proof_last() {
        let data1 = vec![b"hello"; 33];
        let tree1 = MerkleTree::new(&data1);
        let root = tree1.get_root();

        let proof = tree1.create_proof(31);
        assert!(!MerkleTree::check_proof_last(b"hello", 31, root, &proof));

        let proof = tree1.create_proof(32);
        assert!(MerkleTree::check_proof_last(b"hello", 32, root, &proof));
    }
}
