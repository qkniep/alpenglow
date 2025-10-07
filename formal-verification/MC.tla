---- MODULE MC ----
EXTENDS Alpenglow

\* Model constants
Validators <- {"v1", "v2", "v3", "v4"}
MaxSlot <- 3
FastThreshold <- 80
SlowThreshold <- 60
MaxByzantine <- 1

\* Model constraints
HonestByzantine <- {} \* No Byzantine faults for initial model

\* Initial state constraints
Init ==
    /\ currentSlot = 0
    /\ blocks = [s \in Slots |-> [type |-> "empty", slot |-> s, parent |-> "genesis"]]
    /\ votes = [v \in Validators |-> [s \in Slots |-> "none"]]
    /\ certificates = [s \in Slots |-> [t \in CertType |-> [signers |-> {}, block |-> "none"]]]
    /\ finalized = {}
    /\ leaders = [s \in Slots |-> CHOOSE v \in Validators: TRUE]
    /\ timeouts = [s \in Slots |-> 0]
    /\ network = {}

\* Fairness and symmetry constraints
Fairness == TRUE \* No fairness constraints for initial model

\* Properties to check
Safety == NoConflictingFinalizations
Liveness == Progress
Uniqueness == UniqueCertificates

====