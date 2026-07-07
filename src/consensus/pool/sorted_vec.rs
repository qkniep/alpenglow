// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tiny sorted-vector map and set backed by inline [`SmallVec`] storage.
//!
//! These provide the handful of `BTreeMap`/`BTreeSet`-like operations
//! that [`pool`](super) needs for its per-slot, per-block-hash bookkeeping.
//! A slot almost always tracks a single block,
//! so keeping that entry inline avoids heap allocations in the common case.
//! The entries still need to be able to grow to handle equivocation.
//! Entries are kept sorted so lookups stay `O(log n)`.

use smallvec::SmallVec;

/// Sorted-vector map keeping a single entry inline before spilling to the heap.
#[derive(Clone, Debug)]
pub(super) struct SortedVecMap<K, V>(SmallVec<[(K, V); 1]>);

impl<K, V> Default for SortedVecMap<K, V> {
    fn default() -> Self {
        Self(SmallVec::new())
    }
}

impl<K: Ord, V> SortedVecMap<K, V> {
    /// Creates an empty map.
    pub(super) fn empty() -> Self {
        Self::default()
    }

    /// Returns a reference to the value for `key`, if present.
    pub(super) fn get(&self, key: &K) -> Option<&V> {
        self.search(key).ok().map(|i| &self.0[i].1)
    }

    /// Returns a mutable reference to the value for `key`, if present.
    pub(super) fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        match self.search(key) {
            Ok(i) => Some(&mut self.0[i].1),
            Err(_) => None,
        }
    }

    /// Returns a mutable reference to the value for `key`,
    /// first inserting the result of `default` if the key is absent.
    ///
    /// Does a single lookup and clones `key` only when inserting.
    pub(super) fn get_or_insert_with(&mut self, key: &K, default: impl FnOnce() -> V) -> &mut V
    where
        K: Clone,
    {
        let index = match self.search(key) {
            Ok(index) => index,
            Err(index) => {
                self.0.insert(index, (key.clone(), default()));
                index
            }
        };
        &mut self.0[index].1
    }

    fn search(&self, key: &K) -> Result<usize, usize> {
        self.0.binary_search_by(|(k, _)| k.cmp(key))
    }
}

/// Sorted-vector set keeping a single element inline before spilling to the heap.
#[derive(Clone, Debug)]
pub(super) struct SortedVecSet<T>(SmallVec<[T; 1]>);

impl<T> Default for SortedVecSet<T> {
    fn default() -> Self {
        Self(SmallVec::new())
    }
}

impl<T: Ord> SortedVecSet<T> {
    /// Creates an empty set.
    pub(super) fn empty() -> Self {
        Self::default()
    }

    /// Inserts `value`, returning `true` if it was not already present.
    pub(super) fn insert(&mut self, value: T) -> bool {
        match self.0.binary_search(&value) {
            Ok(_) => false,
            Err(index) => {
                self.0.insert(index, value);
                true
            }
        }
    }

    /// Returns whether `value` is in the set.
    pub(super) fn contains(&self, value: &T) -> bool {
        self.0.binary_search(value).is_ok()
    }

    /// Removes `value`, returning `true` if it was present.
    pub(super) fn remove(&mut self, value: &T) -> bool {
        match self.0.binary_search(value) {
            Ok(index) => {
                self.0.remove(index);
                true
            }
            Err(_) => false,
        }
    }
}

impl<T> IntoIterator for SortedVecSet<T> {
    type Item = T;
    type IntoIter = smallvec::IntoIter<[T; 1]>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_get_or_insert_with() {
        let mut map: SortedVecMap<u32, u64> = SortedVecMap::empty();

        // inserts the default when absent
        *map.get_or_insert_with(&7, || 0) += 5;
        assert_eq!(map.get(&7), Some(&5));

        // reuses the existing entry when present
        *map.get_or_insert_with(&7, || 100) += 3;
        assert_eq!(map.get(&7), Some(&8));

        assert_eq!(map.get(&9), None);
        assert_eq!(map.get_mut(&9), None);
    }

    #[test]
    fn map_stays_sorted_when_spilling() {
        let mut map: SortedVecMap<u32, u32> = SortedVecMap::empty();
        for k in [5, 1, 9, 3, 7, 0] {
            map.get_or_insert_with(&k, || k);
        }
        let keys: Vec<u32> = map.0.iter().map(|(k, _)| *k).collect();
        assert_eq!(keys, [0, 1, 3, 5, 7, 9]);
        for k in [5, 1, 9, 3, 7, 0] {
            assert_eq!(map.get(&k), Some(&k));
        }
    }

    #[test]
    fn set_insert_contains_iter() {
        let mut set: SortedVecSet<u32> = SortedVecSet::empty();
        assert!(set.insert(3));
        assert!(set.insert(1));
        assert!(set.insert(5));
        assert!(!set.insert(3)); // duplicate
        assert!(set.contains(&1));
        assert!(!set.contains(&2));

        assert!(set.remove(&1));
        assert!(!set.remove(&1)); // already gone
        assert!(!set.contains(&1));

        let collected: Vec<u32> = set.into_iter().collect();
        assert_eq!(collected, [3, 5]); // sorted, with the removed element gone
    }
}
