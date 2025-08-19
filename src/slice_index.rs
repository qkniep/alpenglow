use serde::{Deserialize, Serialize};

const MAX_SLICES_PER_BLOCK: usize = 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, PartialOrd, Ord)]
pub struct SliceIndex(usize);

impl SliceIndex {
    #[cfg(test)]
    pub(crate) fn new(index: usize) -> Self {
        assert!(index < MAX_SLICES_PER_BLOCK);
        Self(index)
    }

    pub(crate) fn inner(self) -> usize {
        self.0
    }

    pub(crate) fn first() -> Self {
        Self(0)
    }

    pub(crate) fn is_first(&self) -> bool {
        self.0 == 0
    }

    pub(crate) fn is_last(&self) -> bool {
        self.0 == MAX_SLICES_PER_BLOCK - 1
    }

    pub(crate) fn all() -> impl Iterator<Item = Self> {
        (0..MAX_SLICES_PER_BLOCK).map(Self)
    }

    pub(crate) fn until(&self) -> impl Iterator<Item = Self> {
        (0..=self.0).map(Self)
    }
}
