// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Copy-on-write account state for the execution engine.
//!
//! [`State`] maps fixed-size [`Address`]es to arbitrary [`AccountData`] bytes.
//! It is implemented as a bitmap-compressed 32-way trie (HAMT) over the bits
//! of the address. Since addresses are assumed to be uniformly distributed
//! (e.g. hashes or public keys), the trie stays shallow and balanced without
//! hashing keys or any explicit rebalancing.
//!
//! All nodes are reference-counted and shared between copies of the state:
//! cloning a [`State`] is O(1) and a mutation copies only the path from the
//! root to the affected leaf (path copying). This makes it cheap to maintain
//! one state per unfinalized block in the block tree, forking the parent
//! block's state on [`begin_block`] and dropping unreachable forks on
//! [`finalize`].
//!
//! The trie structure is canonical: it depends only on the contents of the
//! state, not on the order of operations that produced them. Equality between
//! states is therefore plain structural equality.
//!
//! [`begin_block`]: super::ExecutionEngine::begin_block
//! [`finalize`]: super::ExecutionEngine::finalize

use std::mem;
use std::sync::Arc;

use smallvec::SmallVec;

/// Unique fixed-size identifier of an entry in the [`State`].
///
/// Addresses are assumed to be uniformly distributed bit strings,
/// e.g. hashes or public keys.
pub type Address = [u8; 32];

/// Raw value bytes stored under an [`Address`].
pub type AccountData = Vec<u8>;

/// Number of address bits consumed per trie level.
const BITS_PER_LEVEL: usize = 5;

/// Branching factor of the trie.
const FANOUT: u32 = 1 << BITS_PER_LEVEL;

/// Copy-on-write map from [`Address`] to [`AccountData`].
///
/// See the [module documentation](self) for design details.
///
/// # Examples
///
/// ```
/// use alpenglow::execution::state::State;
///
/// let mut state = State::new();
/// state.insert([1; 32], vec![42]);
///
/// // Forking is O(1); forks share unmodified structure.
/// let mut fork = state.clone();
/// fork.insert([2; 32], vec![43]);
///
/// assert_eq!(state.get(&[2; 32]), None);
/// assert_eq!(fork.get(&[2; 32]), Some([43].as_slice()));
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct State {
    /// Root node of the trie, always a [`Node::Branch`].
    root: Arc<Node>,
    /// Number of entries in the state.
    len: usize,
}

impl State {
    /// Creates a new empty state.
    #[must_use]
    pub fn new() -> Self {
        Self {
            root: Arc::new(Node::Branch(Branch::default())),
            len: 0,
        }
    }

    /// Returns the number of entries in the state.
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the state contains no entries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the value stored under `key`, if any.
    #[must_use]
    pub fn get(&self, key: &Address) -> Option<&[u8]> {
        let mut node = self.root.as_ref();
        let mut depth = 0;
        loop {
            match node {
                Node::Branch(branch) => {
                    let idx = branch.child_index(chunk_at(key, depth))?;
                    node = branch.children[idx].as_ref();
                    depth += 1;
                }
                Node::Leaf(leaf) => {
                    return (&leaf.key == key).then_some(leaf.value.as_slice());
                }
            }
        }
    }

    /// Inserts `value` under `key`, returning the previously stored value, if any.
    pub fn insert(&mut self, key: Address, value: AccountData) -> Option<AccountData> {
        let old = Self::insert_rec(&mut self.root, 0, key, value);
        if old.is_none() {
            self.len += 1;
        }
        old
    }

    /// Removes the value stored under `key` and returns it, if any.
    pub fn remove(&mut self, key: &Address) -> Option<AccountData> {
        // Fast path: avoid copying any nodes if the key is not present.
        self.get(key)?;
        let old = Self::remove_rec(&mut self.root, 0, key)
            .expect("key was found by the lookup right before");
        self.len -= 1;
        Some(old)
    }

    /// Returns an iterator over all entries in lexicographic key order.
    #[must_use]
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            stack: vec![self.root.as_ref()],
        }
    }

    /// Recursive helper for [`insert`](Self::insert).
    ///
    /// `node` must be a branch node sitting at the given `depth` of the trie.
    fn insert_rec(
        node: &mut Arc<Node>,
        depth: usize,
        key: Address,
        value: AccountData,
    ) -> Option<AccountData> {
        let Node::Branch(branch) = Arc::make_mut(node) else {
            unreachable!("insert_rec is only called on branch nodes");
        };
        let chunk = chunk_at(&key, depth);
        let Some(idx) = branch.child_index(chunk) else {
            // Empty slot: insert a new leaf here.
            branch.insert_child(chunk, Arc::new(Node::Leaf(Leaf { key, value })));
            return None;
        };

        // Occupied slot: descend into branches, replace or split leaves.
        let child = &mut branch.children[idx];
        if matches!(child.as_ref(), Node::Branch(_)) {
            return Self::insert_rec(child, depth + 1, key, value);
        }
        let Node::Leaf(leaf) = Arc::make_mut(child) else {
            unreachable!("non-branch nodes are leaves");
        };
        if leaf.key == key {
            // Same key: replace the value in place.
            return Some(mem::replace(&mut leaf.value, value));
        }
        // Different key: split into a subtree holding both leaves.
        let existing = Leaf {
            key: leaf.key,
            value: mem::take(&mut leaf.value),
        };
        *child = Arc::new(split_leaves(depth + 1, existing, Leaf { key, value }));
        None
    }

    /// Recursive helper for [`remove`](Self::remove).
    ///
    /// `node` must be a branch node sitting at the given `depth` of the trie.
    fn remove_rec(node: &mut Arc<Node>, depth: usize, key: &Address) -> Option<AccountData> {
        let Node::Branch(branch) = Arc::make_mut(node) else {
            unreachable!("remove_rec is only called on branch nodes");
        };
        let chunk = chunk_at(key, depth);
        let idx = branch.child_index(chunk)?;

        // Check whether the child is a leaf, and if so whether it matches `key`.
        let leaf_matches = match branch.children[idx].as_ref() {
            Node::Leaf(leaf) => Some(&leaf.key == key),
            Node::Branch(_) => None,
        };
        match leaf_matches {
            // Some other entry's leaf occupies this slot: `key` is not present.
            Some(false) => None,
            // Found the entry: remove the leaf.
            Some(true) => {
                let removed = branch.remove_child(idx, chunk);
                Some(take_leaf_value(removed))
            }
            // The child is a branch: recurse, then restore canonical structure.
            None => {
                let child = &mut branch.children[idx];
                let value = Self::remove_rec(child, depth + 1, key)?;
                // If the child branch is left with a single leaf child,
                // collapse it into that leaf.
                let collapse = match child.as_ref() {
                    Node::Branch(b) if b.children.len() == 1 => match b.children[0].as_ref() {
                        Node::Leaf(_) => Some(Arc::clone(&b.children[0])),
                        Node::Branch(_) => None,
                    },
                    _ => None,
                };
                if let Some(leaf) = collapse {
                    *child = leaf;
                }
                Some(value)
            }
        }
    }
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> IntoIterator for &'a State {
    type Item = (&'a Address, &'a [u8]);
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterator over the entries of a [`State`] in lexicographic key order.
pub struct Iter<'a> {
    /// Stack of nodes still to be visited.
    ///
    /// Children of visited branches are pushed in reverse chunk order, so
    /// nodes are popped in increasing chunk order (lexicographic key order).
    stack: Vec<&'a Node>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = (&'a Address, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.stack.pop()? {
                Node::Leaf(leaf) => return Some((&leaf.key, leaf.value.as_slice())),
                Node::Branch(branch) => {
                    let children = branch.children.iter().rev();
                    self.stack.extend(children.map(|child| child.as_ref()));
                }
            }
        }
    }
}

/// A node in the trie.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Node {
    /// Inner node, holding one child per occupied chunk.
    Branch(Branch),
    /// Leaf node, holding a single entry.
    Leaf(Leaf),
}

/// Inner node of the trie.
///
/// Canonical structure invariant: every branch except the root either has at
/// least two children, or has a single child that is itself a branch. Branches
/// left with a single leaf child are collapsed into that leaf on removal.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Branch {
    /// Bitmap of occupied child slots: bit `c` is set iff a child for chunk `c` exists.
    bitmap: u32,
    /// Children in increasing chunk order, one per set bit in `bitmap`.
    children: SmallVec<[Arc<Node>; 4]>,
}

/// Leaf node of the trie, holding a single entry.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Leaf {
    /// Full address of this entry.
    key: Address,
    /// Value bytes of this entry.
    value: AccountData,
}

impl Branch {
    /// Returns the index into `children` of the child for `chunk`, if it exists.
    fn child_index(&self, chunk: u32) -> Option<usize> {
        if self.bitmap & (1 << chunk) == 0 {
            None
        } else {
            Some((self.bitmap & ((1 << chunk) - 1)).count_ones() as usize)
        }
    }

    /// Inserts a new child for `chunk`, which must not be occupied yet.
    fn insert_child(&mut self, chunk: u32, child: Arc<Node>) {
        debug_assert_eq!(self.bitmap & (1 << chunk), 0, "child slot must be empty");
        let idx = (self.bitmap & ((1 << chunk) - 1)).count_ones() as usize;
        self.bitmap |= 1 << chunk;
        self.children.insert(idx, child);
    }

    /// Removes and returns the child at index `idx`, occupying `chunk`.
    fn remove_child(&mut self, idx: usize, chunk: u32) -> Arc<Node> {
        debug_assert_ne!(self.bitmap & (1 << chunk), 0, "child slot must be occupied");
        self.bitmap &= !(1 << chunk);
        self.children.remove(idx)
    }
}

/// Extracts the chunk of `key` indexing into a branch node at `depth`.
///
/// The address is interpreted as a big-endian bit string and split into
/// consecutive [`BITS_PER_LEVEL`]-bit chunks, the last one padded with zero
/// bits. Trie order thus equals lexicographic key order.
fn chunk_at(key: &Address, depth: usize) -> u32 {
    let bit = depth * BITS_PER_LEVEL;
    debug_assert!(bit < key.len() * 8, "depth out of range");
    let hi = u16::from(key[bit / 8]) << 8;
    let lo = key.get(bit / 8 + 1).copied().map_or(0, u16::from);
    let window = u32::from(hi | lo);
    (window >> (16 - BITS_PER_LEVEL - bit % 8)) & (FANOUT - 1)
}

/// Builds the minimal subtree at `depth` distinguishing two leaves.
///
/// The leaves must have distinct keys. Creates a chain of single-child
/// branches down to the first chunk in which the two keys differ.
fn split_leaves(depth: usize, leaf1: Leaf, leaf2: Leaf) -> Node {
    debug_assert_ne!(leaf1.key, leaf2.key, "leaves must have distinct keys");
    let chunk1 = chunk_at(&leaf1.key, depth);
    let chunk2 = chunk_at(&leaf2.key, depth);
    let mut branch = Branch::default();
    if chunk1 == chunk2 {
        let child = Arc::new(split_leaves(depth + 1, leaf1, leaf2));
        branch.insert_child(chunk1, child);
    } else {
        branch.insert_child(chunk1, Arc::new(Node::Leaf(leaf1)));
        branch.insert_child(chunk2, Arc::new(Node::Leaf(leaf2)));
    }
    Node::Branch(branch)
}

/// Extracts the value from a leaf node, avoiding a copy if the node is not shared.
fn take_leaf_value(node: Arc<Node>) -> AccountData {
    match Arc::try_unwrap(node) {
        Ok(Node::Leaf(leaf)) => leaf.value,
        Ok(Node::Branch(_)) => unreachable!("only called on leaf nodes"),
        Err(node) => match node.as_ref() {
            Node::Leaf(leaf) => leaf.value.clone(),
            Node::Branch(_) => unreachable!("only called on leaf nodes"),
        },
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use rand::prelude::*;

    use super::*;

    /// Returns a random address.
    fn random_address(rng: &mut impl Rng) -> Address {
        let mut address = [0; 32];
        rng.fill_bytes(&mut address);
        address
    }

    /// Returns a random account value.
    fn random_value(rng: &mut impl Rng) -> AccountData {
        let mut value = vec![0; rng.random_range(1..16)];
        rng.fill_bytes(&mut value);
        value
    }

    #[test]
    fn insert_get_remove() {
        let mut state = State::new();
        assert!(state.is_empty());
        assert_eq!(state.get(&[0; 32]), None);
        assert_eq!(state.remove(&[0; 32]), None);

        assert_eq!(state.insert([0; 32], vec![1, 2, 3]), None);
        assert_eq!(state.len(), 1);
        assert_eq!(state.get(&[0; 32]), Some([1, 2, 3].as_slice()));

        // Overwriting returns the previous value.
        assert_eq!(state.insert([0; 32], vec![4]), Some(vec![1, 2, 3]));
        assert_eq!(state.len(), 1);
        assert_eq!(state.get(&[0; 32]), Some([4].as_slice()));

        assert_eq!(state.remove(&[0; 32]), Some(vec![4]));
        assert!(state.is_empty());
        assert_eq!(state.get(&[0; 32]), None);
    }

    #[test]
    fn matches_reference_model() {
        let mut rng = rand::rng();
        let mut state = State::new();
        let mut reference = BTreeMap::new();

        // Use a small key pool so that updates and removals hit existing entries.
        let keys: Vec<Address> = (0..64).map(|_| random_address(&mut rng)).collect();

        for _ in 0..1000 {
            let key = keys[rng.random_range(0..keys.len())];
            if rng.random_bool(0.7) {
                let value = random_value(&mut rng);
                assert_eq!(
                    state.insert(key, value.clone()),
                    reference.insert(key, value)
                );
            } else {
                assert_eq!(state.remove(&key), reference.remove(&key));
            }
            assert_eq!(state.len(), reference.len());
        }

        // Iteration yields the same entries in the same (lexicographic) order.
        let state_entries = state.iter();
        let reference_entries = reference.iter().map(|(k, v)| (k, v.as_slice()));
        assert!(state_entries.eq(reference_entries));

        // Point lookups agree on every key.
        for key in &keys {
            assert_eq!(state.get(key), reference.get(key).map(Vec::as_slice));
        }
    }

    #[test]
    fn forks_are_independent() {
        let mut rng = rand::rng();
        let mut state = State::new();
        let keys: Vec<Address> = (0..100).map(|_| random_address(&mut rng)).collect();
        for key in &keys {
            state.insert(*key, vec![0]);
        }

        // Forks share structure with the original state.
        let mut fork = state.clone();
        assert!(Arc::ptr_eq(&state.root, &fork.root));

        // Writes to the fork are not visible in the original, and vice versa.
        fork.insert(keys[0], vec![1]);
        fork.remove(&keys[1]);
        let new_key = random_address(&mut rng);
        state.insert(new_key, vec![2]);

        assert_eq!(state.get(&keys[0]), Some([0].as_slice()));
        assert_eq!(fork.get(&keys[0]), Some([1].as_slice()));
        assert_eq!(state.get(&keys[1]), Some([0].as_slice()));
        assert_eq!(fork.get(&keys[1]), None);
        assert_eq!(state.get(&new_key), Some([2].as_slice()));
        assert_eq!(fork.get(&new_key), None);

        // Untouched entries remain visible in both.
        for key in &keys[2..] {
            assert_eq!(state.get(key), Some([0].as_slice()));
            assert_eq!(state.get(key), fork.get(key));
        }
    }

    #[test]
    fn structure_is_canonical() {
        let mut rng = rand::rng();
        let entries: Vec<(Address, AccountData)> = (0..100)
            .map(|_| (random_address(&mut rng), random_value(&mut rng)))
            .collect();

        // The same entries inserted in different orders produce equal states.
        let mut forward = State::new();
        for (key, value) in &entries {
            forward.insert(*key, value.clone());
        }
        let mut backward = State::new();
        for (key, value) in entries.iter().rev() {
            backward.insert(*key, value.clone());
        }
        assert_eq!(forward, backward);

        // Inserting and removing unrelated entries leaves no trace.
        let mut with_extra = State::new();
        let extra: Vec<Address> = (0..50).map(|_| random_address(&mut rng)).collect();
        for key in &extra {
            with_extra.insert(*key, vec![255]);
        }
        for (key, value) in &entries {
            with_extra.insert(*key, value.clone());
        }
        for key in &extra {
            with_extra.remove(key);
        }
        assert_eq!(forward, with_extra);

        // Removing everything returns to the empty state.
        for (key, _) in &entries {
            with_extra.remove(key);
        }
        assert_eq!(with_extra, State::new());
    }

    #[test]
    fn handles_long_shared_prefixes() {
        // Keys sharing a 255-bit prefix force the trie to its maximum depth.
        let key_a = [0xAB; 32];
        let mut key_b = [0xAB; 32];
        key_b[31] ^= 0x01;

        let mut state = State::new();
        assert_eq!(state.insert(key_a, vec![1]), None);
        assert_eq!(state.insert(key_b, vec![2]), None);
        assert_eq!(state.len(), 2);
        assert_eq!(state.get(&key_a), Some([1].as_slice()));
        assert_eq!(state.get(&key_b), Some([2].as_slice()));

        // Removing one entry collapses the deep chain of branches: the result
        // is structurally identical to a state only ever containing the other.
        assert_eq!(state.remove(&key_a), Some(vec![1]));
        let mut expected = State::new();
        expected.insert(key_b, vec![2]);
        assert_eq!(state, expected);
    }

    #[test]
    fn iterates_in_key_order() {
        let mut rng = rand::rng();
        let mut state = State::new();
        let mut keys: Vec<Address> = (0..200).map(|_| random_address(&mut rng)).collect();
        for key in &keys {
            state.insert(*key, key.to_vec());
        }

        keys.sort_unstable();
        let iterated: Vec<Address> = state.iter().map(|(key, _)| *key).collect();
        assert_eq!(iterated, keys);

        // Each entry's value matches its key.
        for (key, value) in &state {
            assert_eq!(key.as_slice(), value);
        }
    }

    #[test]
    fn state_is_send_and_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<State>();
    }
}
