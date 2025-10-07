---------------------------- MODULE Rotor -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Validators, MaxSlot, TotalStake, TotalShreds

ASSUME /\ Validators # {} /\ MaxSlot \in Nat /\ MaxSlot > 0 /\ TotalStake \in Nat \ {0} /\ TotalShreds \in Nat \ {0}

Slots == 1..MaxSlot
ShredIndices == 0..(TotalShreds - 1)
ValidatorIds == {v.id : v \in Validators}

StakePerValidator == TotalStake \div Cardinality(Validators)

(* Stake-weighted sampling function - simplified for TLA+ *)
StakeWeight(S) == Cardinality(S) * StakePerValidator

(* Deterministic relay sampling based on slot and shred index *)
SampleRelay(slot, shredIndex, validators) ==
    LET seed == (slot * TotalShreds) + shredIndex
        index == seed % Cardinality(validators)
    IN  CHOOSE v \in validators: TRUE  \* Simplified - in practice uses stake-weighted sampling

VARIABLES
    shreds,           \* Map from [slot, shredIndex] to shred content
    shredLocations,   \* Map from [slot, shredIndex] to set of validators that have the shred
    relays            \* Map from [slot, shredIndex] to relay validator

vars == <<shreds, shredLocations, relays>>

Init ==
    /\ shreds = [slot \in Slots |-> [shredIndex \in ShredIndices |-> [slot |-> slot, index |-> shredIndex]]]
    /\ shredLocations = [slot \in Slots |-> [shredIndex \in ShredIndices |-> {}]]
    /\ relays = [slot \in Slots |-> [shredIndex \in ShredIndices |-> SampleRelay(slot, shredIndex, ValidatorIds)]]

(* Leader sends shred to its designated relay *)
SendToRelay(v, slot, shredIndex) ==
    LET relay == relays[slot][shredIndex]
    IN  /\ relay # v  \* Don't send to self
        /\ shredLocations' = [shredLocations EXCEPT ![slot][shredIndex] = @ \union {relay}]
        /\ UNCHANGED <<shreds, relays>>

(* Relay broadcasts shred to all other validators except leader *)
RelayBroadcast(relay, slot, shredIndex) ==
    LET leader == SampleRelay(slot, shredIndex, ValidatorIds)  \* Simplified leader selection
        recipients == (ValidatorIds \ {leader, relay})
    IN  /\ relays[slot][shredIndex] = relay  \* This validator is the relay
        /\ shredLocations' = [shredLocations EXCEPT ![slot][shredIndex] = @ \union recipients]
        /\ UNCHANGED <<shreds, relays>>

(* Combined action: leader sends, then relay broadcasts *)
DisseminateShred(slot, shredIndex) ==
    LET leader == SampleRelay(slot, shredIndex, ValidatorIds)
        relay == relays[slot][shredIndex]
    IN  /\ relay # leader  \* Relay different from leader
        /\ shredLocations[slot][shredIndex] = {}  \* Not yet disseminated
        /\ shredLocations' = [shredLocations EXCEPT ![slot][shredIndex] = ValidatorIds \ {leader}]
        /\ UNCHANGED <<shreds, relays>>

Next ==
    \/ \E slot \in Slots, shredIndex \in ShredIndices:
         DisseminateShred(slot, shredIndex)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

(* Safety Properties *)

(* All shreds eventually reach all validators except the leader *)
AllShredsDelivered ==
    \A slot \in Slots, shredIndex \in ShredIndices:
        LET leader == SampleRelay(slot, shredIndex, ValidatorIds)
        IN  shredLocations[slot][shredIndex] = (ValidatorIds \ {leader})

(* No shred is lost *)
NoShredLoss ==
    \A slot \in Slots, shredIndex \in ShredIndices:
        shredLocations[slot][shredIndex] # {}

(* Relays are properly assigned *)
ValidRelays ==
    \A slot \in Slots, shredIndex \in ShredIndices:
        relays[slot][shredIndex] \in ValidatorIds

(* Liveness Properties *)

(* Eventually all shreds are delivered *)
<>[](\A slot \in Slots, shredIndex \in ShredIndices:
       shredLocations[slot][shredIndex] # {})

(* Progress: system can always make dissemination progress *)
Progress ==
    []<>(ENABLED Next)

=============================================================================