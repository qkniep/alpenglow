// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//!

use std::ops::{Deref, DerefMut};
use std::sync::{Arc, Mutex};

use super::Shredder;

///
pub struct ShredderPool<S: Shredder> {
    shredders: Arc<Mutex<Vec<S>>>,
}

impl<S: Shredder> ShredderPool<S> {
    ///
    pub fn new(shredders: Vec<S>) -> Self {
        Self {
            shredders: Arc::new(Mutex::new(shredders)),
        }
    }

    ///
    pub fn take(&self) -> ShredderGuard<S> {
        ShredderGuard {
            pool: self.shredders.clone(),
            shredder: self.shredders.lock().unwrap().pop(),
        }
    }
}

impl<S: Shredder + Default> ShredderPool<S> {
    ///
    pub fn with_size(size: usize) -> Self {
        let shredders = (0..size).map(|_| S::default()).collect::<Vec<_>>();
        Self::new(shredders)
    }
}

///
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
