#![no_main]

use alpenglow::consensus::ConsensusMessage;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _res = wincode::deserialize::<ConsensusMessage>(data);
});
