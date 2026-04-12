#![no_main]

use alpenglow::shredder::Shred;
use libfuzzer_sys::fuzz_target;

// Fuzz serialization roundtrip consistency for Shred using structure-aware fuzzing.
// Every input is a valid Shred (generated via Arbitrary), so all inputs exercise
// the roundtrip logic rather than being discarded at the deserialization step.
//
// Invariant: re-serializing a deserialized Shred must yield identical bytes.
fuzz_target!(|shred: Shred| {
    let serialized = wincode::serialize(&shred).expect("serialization must not fail");
    let shred2 = wincode::deserialize::<Shred>(&serialized)
        .expect("deserializing serialized data must not fail");
    let serialized2 = wincode::serialize(&shred2).expect("second serialization must not fail");

    assert_eq!(
        serialized, serialized2,
        "roundtrip serialization produced different bytes"
    );
});
