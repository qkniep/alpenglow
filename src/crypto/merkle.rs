// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use super::{Hash, hash};

const LEAF_LABEL: [u8; 22] = *b"\x00ALPENGLOW-MERKLE-TREE";
const LEFT_LABEL: [u8; 22] = *b"\x01ALPENGLOW-MERKLE-TREE";
const RIGHT_LABEL: [u8; 22] = *b"\x02ALPENGLOW-MERKLE-TREE";

/// Implementation of a Merkle tree.
/// This implementation non-power-of-two leaf count by adding empty leaves.
pub struct MerkleTree {
    nodes: Vec<Hash>,
    height: usize,
}

impl MerkleTree {
    pub fn new(data: &[impl AsRef<[u8]>]) -> Self {
        let mut nodes = Vec::new();
        let mut height = 0;

        // calculate leaf hashes
        for leaf in data {
            let leaf_hash = hash_leaf(leaf.as_ref());
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

    /// Returns `true` iff `proof` is a valid Merkle path for a leaf containing
    /// `data` at the given `index` in the given Merkle root.
    #[must_use]
    pub fn check_proof(data: &[u8], index: usize, root: Hash, proof: &[Hash]) -> bool {
        let mut i = index;
        let mut node = hash_leaf(data);
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
    hash(&[&LEAF_LABEL[..], data].concat())
}

/// Hashes a pair of child hashes into a parent non-leaf node with labels.
///
/// The labels prevent the possibility to claim an intermediate node was a leaf.
/// They also make the Merkle tree more robust against pre-calculation attacks.
fn hash_pair(left: Hash, right: Hash) -> Hash {
    hash(&[&LEFT_LABEL[..], &left, &RIGHT_LABEL[..], &right].concat())
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
}
