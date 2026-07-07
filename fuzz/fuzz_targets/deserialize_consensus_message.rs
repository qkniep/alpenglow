// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

#![no_main]

use alpenglow::consensus::ConsensusMessage;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _res = alpenglow::network::deserialize::<ConsensusMessage>(data);
});
