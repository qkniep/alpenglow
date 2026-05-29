#![no_main]

use alpenglow::repair::RepairRequest;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _res = wincode::deserialize::<RepairRequest>(data);
});
