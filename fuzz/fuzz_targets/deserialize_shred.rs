#![no_main]

use alpenglow::shredder::Shred;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _res = wincode::deserialize::<Shred>(data);
});
