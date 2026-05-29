#![no_main]

use alpenglow::consensus::ConsensusMessage;
use libfuzzer_sys::fuzz_target;

// Fuzz serialization roundtrip consistency for ConsensusMessage.
// If arbitrary bytes successfully deserialize into a ConsensusMessage,
// re-serializing and deserializing again must produce identical bytes.
// A mismatch indicates a serialization/deserialization asymmetry bug.
fuzz_target!(|data: &[u8]| {
    let Ok(msg) = wincode::deserialize::<ConsensusMessage>(data) else {
        return;
    };

    let serialized = wincode::serialize(&msg).expect("re-serialization must not fail");
    let msg2 = wincode::deserialize::<ConsensusMessage>(&serialized)
        .expect("deserializing re-serialized data must not fail");
    let serialized2 = wincode::serialize(&msg2).expect("second re-serialization must not fail");

    assert_eq!(
        serialized, serialized2,
        "roundtrip serialization produced different bytes"
    );
});
