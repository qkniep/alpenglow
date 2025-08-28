// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use crate::Transaction;
use crate::crypto::Hash;

/// A bundle of transactions to execute.
pub struct ExecutionBundle(Vec<Transaction>);

///
pub trait Execution {
    ///
    fn execute_bundle(&mut self, bundle: ExecutionBundle);
}

///
pub struct DummyExecution;

impl Execution for DummyExecution {
    fn execute_bundle(&mut self, _bundle: ExecutionBundle) {}
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic() {}
}
