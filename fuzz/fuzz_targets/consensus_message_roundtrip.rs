#![no_main]

use alpenglow::consensus::ConsensusMessage;
use libfuzzer_sys::fuzz_target;

// Fuzz serialization roundtrip consistency for ConsensusMessage using structure-aware fuzzing.
// Every input is a valid ConsensusMessage (generated via Arbitrary), so all inputs exercise
// the roundtrip logic rather than being discarded at the deserialization step.
//
// Invariant: re-serializing a deserialized ConsensusMessage must yield identical bytes.
fuzz_target!(|msg: ConsensusMessage| {
    let serialized = wincode::serialize(&msg).expect("serialization must not fail");
    let msg2 = wincode::deserialize::<ConsensusMessage>(&serialized)
        .expect("deserializing serialized data must not fail");
    let serialized2 = wincode::serialize(&msg2).expect("second serialization must not fail");

    assert_eq!(
        serialized, serialized2,
        "roundtrip serialization produced different bytes"
    );
});
