#![no_main]

use alpenglow::Transaction;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _res = alpenglow::network::deserialize::<Transaction>(data);
});
