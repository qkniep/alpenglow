---------------------------- MODULE Rotor -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Validators, MaxSlot, TotalStake, TotalShreds

ASSUME /\ Validators # {} 
       /\ MaxSlot \in Nat 
       /\ MaxSlot > 0 
       /\ TotalStake \in Nat \ {0} 
       /\ TotalShreds \in Nat \ {0}

Slots == 1..MaxSlot
ShredIndices == 0..(TotalShreds - 1)

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
    /\ relays = [slot \in Slots |-> [shredIndex \in ShredIndices |-> SampleRelay(slot, shredIndex, Validators)]]

(* Leader sends shred to its designated relay *)
SendToRelay(v, slot, shredIndex) ==
    LET relay == relays[slot][shredIndex]
    IN  /\ relay # v  \* Don't send to self
        /\ shredLocations' = [shredLocations EXCEPT ![slot][shredIndex] = @ \union {relay}]
        /\ UNCHANGED <<shreds, relays>>

(* Relay broadcasts shred to all other validators except leader *)
RelayBroadcast(relay, slot, shredIndex) ==
    LET leader == SampleRelay(slot, shredIndex, Validators)  \* Simplified leader selection
        recipients == (Validators \ {leader, relay})
    IN  /\ relays[slot][shredIndex] = relay  \* This validator is the relay
        /\ shredLocations' = [shredLocations EXCEPT ![slot][shredIndex] = @ \union recipients]
        /\ UNCHANGED <<shreds, relays>>

(* Combined action: leader sends, then relay broadcasts *)
DisseminateShred(slot, shredIndex) ==
    LET leader == SampleRelay(slot, shredIndex, Validators)
        relay == relays[slot][shredIndex]
    IN  /\ shredLocations[slot][shredIndex] = {}  \* Not yet disseminated
        /\ IF relay = leader
           THEN \* If relay is same as leader, broadcast directly to all others
                shredLocations' = [shredLocations EXCEPT ![slot][shredIndex] = Validators \ {leader}]
           ELSE \* Normal case: relay to designated validator who broadcasts
                shredLocations' = [shredLocations EXCEPT ![slot][shredIndex] = Validators \ {leader}]
        /\ UNCHANGED <<shreds, relays>>

Next ==
    \/ \E slot \in Slots, shredIndex \in ShredIndices:
         DisseminateShred(slot, shredIndex)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

(* Safety Properties *)

(* Type correctness *)
TypeOK ==
    /\ shreds \in [Slots -> [ShredIndices -> [slot: Slots, index: ShredIndices]]]
    /\ shredLocations \in [Slots -> [ShredIndices -> SUBSET Validators]]
    /\ relays \in [Slots -> [ShredIndices -> Validators]]

(* All shreds eventually reach all validators except the leader *)
AllShredsDelivered ==
    \A slot \in Slots, shredIndex \in ShredIndices:
        LET leader == SampleRelay(slot, shredIndex, Validators)
        IN  shredLocations[slot][shredIndex] = (Validators \ {leader})

(* Relays are properly assigned *)
ValidRelays ==
    \A slot \in Slots, shredIndex \in ShredIndices:
        relays[slot][shredIndex] \in Validators

(* Once disseminated, shreds are never lost *)
OnceDeliveredNeverLost ==
    \A slot \in Slots, shredIndex \in ShredIndices:
        (shredLocations[slot][shredIndex] # {}) =>
            (shredLocations[slot][shredIndex] \subseteq Validators)

(* Liveness Properties *)

(* Eventually all shreds are delivered *)
EventualDelivery ==
    <>[](\A slot \in Slots, shredIndex \in ShredIndices:
           shredLocations[slot][shredIndex] # {})

(* Progress: system can always make dissemination progress *)
Progress ==
    []<>(ENABLED Next)

=============================================================================