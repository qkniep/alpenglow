// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0
//
// Source: https://github.com/anza-xyz/agave (with modifications)

//! The `weighted_shuffle` module provides an iterator over shuffled weights.

use std::borrow::Borrow;
use std::ops::{AddAssign, SubAssign};

use rand::distr::uniform::{SampleUniform, UniformSampler};
use rand::prelude::*;

use crate::Stake;

// Each internal tree node has FANOUT many child nodes with indices:
//     `(index << BIT_SHIFT) + 1 ..= (index << BIT_SHIFT) + FANOUT`
// Conversely, for each node, the parent node is obtained by:
//     `parent: (index - 1) >> BIT_SHIFT`
// and the subtree weight is stored at
//     `offset: (index - 1) & BIT_MASK`
// of its parent node.
const BIT_SHIFT: usize = 4;
const FANOUT: usize = 1 << BIT_SHIFT;
const BIT_MASK: usize = FANOUT - 1;

/// Implements an iterator where indices are shuffled according to their
/// weights:
///   - Returned indices are unique in the range `[0, weights.len())`.
///   - Higher weighted indices tend to appear earlier proportional to their
///     weight.
///   - Zero weighted indices are shuffled and appear only at the end, after
///     non-zero weighted indices.
#[derive(Clone)]
pub struct WeightedShuffle {
    /// Number of "internal" nodes of the tree.
    num_nodes: usize,
    /// Underlying array implementing the tree.
    /// Nodes without children are never accessed and don't need to be
    /// allocated, so `tree.len() < num_nodes`.
    /// `tree[i][j]` is the sum of all weights in the `j`-th sub-tree of node `i`.
    tree: Vec<[Stake; FANOUT]>,
    /// Current sum of all weights, excluding already sampled ones.
    weight: Stake,
    /// Indices of zero weighted entries.
    zeros: Vec<usize>,
}

impl WeightedShuffle {
    /// If weights are negative or overflow the total sum
    /// they are treated as zero.
    pub fn new<I>(weights: I) -> Self
    where
        I: IntoIterator<Item: Borrow<Stake>>,
        <I as IntoIterator>::IntoIter: ExactSizeIterator,
    {
        let weights = weights.into_iter();
        let (num_nodes, size) = get_num_nodes_and_tree_size(weights.len());
        debug_assert!(size <= num_nodes);
        let mut tree = vec![[0; FANOUT]; size];
        let mut sum: Stake = 0;
        let mut zeros = Vec::default();
        for (k, weight) in weights.enumerate() {
            let weight = *weight.borrow();
            if weight == 0 {
                zeros.push(k);
                continue;
            }
            sum = if let Some(val) = sum.checked_add(weight) {
                val
            } else {
                zeros.push(k);
                continue;
            };
            // Traverse the tree from the leaf node upwards to the root,
            // updating the sub-tree sums along the way.
            let mut index = num_nodes + k; // leaf node
            while index != 0 {
                let offset = (index - 1) & BIT_MASK;
                index = (index - 1) >> BIT_SHIFT; // parent node
                debug_assert!(index < tree.len());
                // SAFETY: Index is updated to a lesser value towards zero.
                // The bitwise AND operation with `BIT_MASK` ensures that offset
                // is always less than `FANOUT`, which is the size of the inner
                // arrays. As a result, `tree[index][offset]` never goes out of
                // bounds.
                unsafe { tree.get_unchecked_mut(index).get_unchecked_mut(offset) }
                    .add_assign(weight);
            }
        }
        Self {
            num_nodes,
            tree,
            weight: sum,
            zeros,
        }
    }

    // Removes given weight at index k.
    fn remove(&mut self, k: usize, weight: Stake) {
        debug_assert!(self.weight >= weight);
        self.weight -= weight;
        // Traverse the tree from the leaf node upwards to the root,
        // updating the sub-tree sums along the way.
        let mut index = self.num_nodes + k; // leaf node
        while index != 0 {
            let offset = (index - 1) & BIT_MASK;
            index = (index - 1) >> BIT_SHIFT; // parent node
            debug_assert!(self.tree[index][offset] >= weight);
            // SAFETY: Index is updated to a lesser value towards zero. The
            // bitwise AND operation with BIT_MASK ensures that offset is
            // always less than FANOUT, which is the size of the inner arrays.
            // As a result, tree[index][offset] never goes out of bounds.
            unsafe { self.tree.get_unchecked_mut(index).get_unchecked_mut(offset) }
                .sub_assign(weight);
        }
    }

    // Returns smallest index such that sum of weights[..=k] > val,
    // along with its respective weight.
    fn search(&self, mut val: Stake) -> (/*index:*/ usize, /*weight:*/ Stake) {
        debug_assert!(val < self.weight);
        debug_assert!(!self.tree.is_empty());
        // Traverse the tree downwards from the root to the target leaf node.
        let mut index = 0; // root
        loop {
            // SAFETY: function returns if index goes out of bounds.
            let (offset, &node) = unsafe { self.tree.get_unchecked(index) }
                .iter()
                .enumerate()
                .find(|&(_, &node)| {
                    if val < node {
                        true
                    } else {
                        val -= node;
                        false
                    }
                })
                .unwrap();
            // Traverse to the subtree of self.tree[index].
            index = (index << BIT_SHIFT) + offset + 1;
            if self.tree.len() <= index {
                return (index - self.num_nodes, node);
            }
        }
    }

    pub fn shuffle<'a, R: Rng>(&'a mut self, rng: &'a mut R) -> impl Iterator<Item = usize> + 'a {
        std::iter::from_fn(move || {
            if self.weight > 0 {
                let sample =
                    <Stake as SampleUniform>::Sampler::sample_single(0, self.weight, rng).unwrap();
                let (index, weight) = self.search(sample);
                self.remove(index, weight);
                return Some(index);
            }
            if self.zeros.is_empty() {
                return None;
            }
            let index =
                <usize as SampleUniform>::Sampler::sample_single(0usize, self.zeros.len(), rng)
                    .unwrap();
            Some(self.zeros.swap_remove(index))
        })
    }
}

// Maps number of items to the number of "internal" nodes of the tree
// which "implicitly" holds those items on the leaves.
// Nodes without children are never accessed and don't need to be
// allocated, so the tree size is the second smaller number.
fn get_num_nodes_and_tree_size(count: usize) -> (/*num_nodes:*/ usize, /*tree_size:*/ usize) {
    let mut size: usize = 0;
    let mut nodes: usize = 1;
    while nodes * FANOUT < count {
        size += nodes;
        nodes *= FANOUT;
    }
    (size + nodes, size + count.div_ceil(FANOUT))
}
