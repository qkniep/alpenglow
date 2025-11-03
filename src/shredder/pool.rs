// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Pool of shredder instances.
//!
//! # Examples
//!
//! Obtain a shredder from the pool, use it, and let it return on drop.
//!
//! ```rust
//! use alpenglow::shredder::{RegularShredder, ShredderPool, Shredder};
//!
//! fn use_shredder<S: Shredder>(shredder: &mut S) {
//!     // ...
//! }
//!
//! let shredder_pool = ShredderPool::<RegularShredder>::with_size(1);
//! {
//!     let mut shredder = shredder_pool.take();
//!     use_shredder(&mut (*shredder));
//!     // shredder is automatically returned to pool when dropped
//! }
//! ```

use std::ops::{Deref, DerefMut};
use std::sync::{Arc, Mutex};

use super::Shredder;

/// A pool of shredders of the same type.
pub struct ShredderPool<S: Shredder> {
    shredders: Arc<Mutex<Vec<S>>>,
}

impl<S: Shredder> ShredderPool<S> {
    /// Creates a new pool with the provided shredders.
    pub fn new(shredders: Vec<S>) -> Self {
        Self {
            shredders: Arc::new(Mutex::new(shredders)),
        }
    }

    /// Takes a shredder from the pool.
    ///
    /// The shredder is automatically returned to the pool when dropped.
    pub fn take(&self) -> ShredderGuard<S> {
        ShredderGuard {
            pool: Arc::clone(&self.shredders),
            shredder: self.shredders.lock().unwrap().pop(),
        }
    }
}

impl<S: Shredder + Default> ShredderPool<S> {
    /// Creates a new pool with `size` shredders.
    pub fn with_size(size: usize) -> Self {
        let shredders = (0..size).map(|_| S::default()).collect::<Vec<_>>();
        Self::new(shredders)
    }
}

/// Guard holding a single shredder from a pool.
///
/// The shredder is automatically returned to the pool when dropped.
pub struct ShredderGuard<S: Shredder> {
    pool: Arc<Mutex<Vec<S>>>,
    shredder: Option<S>,
}

impl<S: Shredder> Deref for ShredderGuard<S> {
    type Target = S;

    fn deref(&self) -> &Self::Target {
        self.shredder.as_ref().unwrap()
    }
}

impl<S: Shredder> DerefMut for ShredderGuard<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.shredder.as_mut().unwrap()
    }
}

impl<S: Shredder> Drop for ShredderGuard<S> {
    fn drop(&mut self) {
        if let Some(shredder) = self.shredder.take() {
            self.pool.lock().unwrap().push(shredder);
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shredder::RegularShredder;

    #[test]
    fn take_sequentially() {
        let shredder_pool = ShredderPool::<RegularShredder>::with_size(1);
        for _ in 0..10 {
            let mut guard = shredder_pool.take();
            let _shredder: &mut RegularShredder = &mut guard;
        }
    }

    #[test]
    fn take_concurrently() {
        let shredder_pool = ShredderPool::<RegularShredder>::with_size(2);

        let mut guard1 = shredder_pool.take();
        let _shredder1: &mut RegularShredder = &mut guard1;
        let mut guard2 = shredder_pool.take();
        let _shredder2: &mut RegularShredder = &mut guard2;

        drop(guard1);
        drop(guard2);
    }
}
