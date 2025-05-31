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

use super::{Hash, hash::hash_all};

const LEAF_LABEL: [u8; 22] = *b"\x00ALPENGLOW-MERKLE-TREE";
const LEFT_LABEL: [u8; 22] = *b"\x01ALPENGLOW-MERKLE-TREE";
const RIGHT_LABEL: [u8; 22] = *b"\x02ALPENGLOW-MERKLE-TREE";

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
}
