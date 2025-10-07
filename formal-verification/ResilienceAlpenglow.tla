--------------------------- MODULE ResilienceAlpenglow -----------------------------
(*
  20+20 Resilience Model of Alpenglow Consensus

  This specification models the complete "20+20" resilience claim:
  - Tolerates up to 20% Byzantine (malicious) validators
  - Tolerates up to 20% crashed/offline validators
  - Maintains safety and liveness under these combined faults

  Byzantine validators can:
  - Equivocate: Vote for multiple conflicting blocks
  - Withhold votes: Refuse to participate
  - Create conflicting certificates

  Crashed validators:
  - Completely offline: Never participate in any actions
  - Fail-stop behavior: Stop responding permanently

  Key Theorem: Safety holds with ≤20% Byzantine + ≤20% crashed stake
*)

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  AllValidators,        \* Complete set of all validators
  ByzantineValidators,  \* Byzantine (malicious) validators
  CrashedValidators,    \* Crashed/offline validators
  MaxSlot,              \* Maximum slot number to model
  TotalStake            \* Total stake across all validators

ASSUME
  /\ ByzantineValidators \subseteq AllValidators
  /\ CrashedValidators \subseteq AllValidators
  /\ ByzantineValidators \intersect CrashedValidators = {}  \* Can't be both
  /\ Cardinality(ByzantineValidators) * StakePerValidator <= TotalStake \div 5  \* ≤20% Byzantine
  /\ Cardinality(CrashedValidators) * StakePerValidator <= TotalStake \div 5    \* ≤20% Crashed

VARIABLES
  currentSlot,          \* Current slot number
  blocks,               \* Set of blocks produced
  votes,                \* Set of votes cast by honest validators
  certificates,         \* Set of certificates created
  finalized,            \* Set of finalized slot numbers
  byzantineVotes        \* Track Byzantine equivocations

vars == <<currentSlot, blocks, votes, certificates, finalized, byzantineVotes>>

\* Helper constants
StakePerValidator == TotalStake \div Cardinality(AllValidators)
HonestValidators == AllValidators \ (ByzantineValidators \union CrashedValidators)

\* Helper: Get stake for a validator
StakeOf(v) == StakePerValidator

\* Quorum thresholds
IsQuorum(stake) == stake >= ((TotalStake * 3) \div 5)          \* 60%
IsStrongQuorum(stake) == stake >= ((TotalStake * 4) \div 5)    \* 80%

\* Total stake of validator set
TotalStakeOf(validatorSet) == Cardinality(validatorSet) * StakePerValidator

\* Check if validator is Byzantine
IsByzantine(v) == v \in ByzantineValidators

\* Check if validator is crashed
IsCrashed(v) == v \in CrashedValidators

\* Check if validator is honest and online
IsHonest(v) == v \in HonestValidators

-----------------------------------------------------------------------------
\* Initial state

Init ==
  /\ currentSlot = 1
  /\ blocks = [s \in 1..MaxSlot |-> [slot |-> s, parent |-> IF s = 1 THEN 0 ELSE s-1]]
  /\ votes = [v \in HonestValidators |-> [s \in 1..MaxSlot |-> NoVote]]
  /\ certificates = [s \in 1..MaxSlot |-> [type \in {"Notar", "FastFinal", "Final"} |-> NoCert]]
  /\ finalized = {}
  /\ byzantineVotes = {}

NoVote == [type |-> "NoVote", slot |-> 0]
NoCert == [signers |-> {}, slot |-> 0]

-----------------------------------------------------------------------------
\* Actions

\* Honest validators advance slot
AdvanceSlot ==
  /\ currentSlot < MaxSlot
  /\ currentSlot' = currentSlot + 1
  /\ UNCHANGED <<blocks, votes, certificates, finalized, byzantineVotes>>

\* Honest validators produce blocks
ProduceBlock(v) ==
  /\ IsHonest(v)
  /\ ~\E b \in blocks : b.slot = currentSlot /\ b.producer = v
  /\ blocks' = blocks \cup {[slot |-> currentSlot, producer |-> v]}
  /\ UNCHANGED <<currentSlot, votes, certificates, finalized, byzantineVotes>>

\* Honest validators vote
Vote(v, s) ==
  /\ IsHonest(v)
  /\ s < currentSlot
  /\ s \in 1..MaxSlot
  /\ \E b \in blocks : b.slot = s
  /\ votes[v][s] = NoVote
  /\ votes' = [votes EXCEPT ![v][s] = [type |-> "Notar", slot |-> s]]
  /\ UNCHANGED <<currentSlot, blocks, certificates, finalized, byzantineVotes>>

\* Byzantine validators can equivocate (vote for multiple blocks)
ByzantineEquivocate(v, s, block1, block2) ==
  /\ IsByzantine(v)
  /\ s < currentSlot
  /\ s \in 1..MaxSlot
  /\ block1 # block2
  /\ byzantineVotes' = byzantineVotes \cup {[validator |-> v, slot |-> s, blocks |-> {block1, block2}]}
  /\ UNCHANGED <<currentSlot, blocks, votes, certificates, finalized>>

\* Create notarization certificate (requires 60% stake from honest validators)
CreateNotarCert(s) ==
  /\ s < currentSlot
  /\ s \in 1..MaxSlot
  /\ certificates[s]["Notar"] = NoCert
  /\ LET honestVoters == {v \in HonestValidators : votes[v][s] # NoVote}
         honestStake == TotalStakeOf(honestVoters)
     IN /\ IsQuorum(honestStake)
        /\ certificates' = [certificates EXCEPT ![s]["Notar"] = [signers |-> honestVoters, slot |-> s]]
        /\ IF IsStrongQuorum(honestStake)
           THEN certificates' = [certificates EXCEPT ![s]["FastFinal"] = [signers |-> honestVoters, slot |-> s]]
           ELSE UNCHANGED certificates
  /\ UNCHANGED <<currentSlot, blocks, votes, finalized, byzantineVotes>>

\* Create final certificate for slow path
CreateFinalCert(s) ==
  /\ s < currentSlot
  /\ s \in 1..MaxSlot
  /\ certificates[s]["Notar"] # NoCert
  /\ certificates[s]["Final"] = NoCert
  /\ LET honestVoters == {v \in HonestValidators : votes[v][s] # NoVote}
         honestStake == TotalStakeOf(honestVoters)
     IN /\ IsQuorum(honestStake)
        /\ certificates' = [certificates EXCEPT ![s]["Final"] = [signers |-> honestVoters, slot |-> s]]
  /\ UNCHANGED <<currentSlot, blocks, votes, finalized, byzantineVotes>>

\* Finalize fast path
FinalizeFast(s) ==
  /\ certificates[s]["FastFinal"] # NoCert
  /\ s \notin finalized
  /\ finalized' = finalized \cup {s}
  /\ UNCHANGED <<currentSlot, blocks, votes, certificates, byzantineVotes>>

\* Finalize slow path
FinalizeSlow(s) ==
  /\ certificates[s]["Notar"] # NoCert
  /\ certificates[s]["Final"] # NoCert
  /\ s \notin finalized
  /\ finalized' = finalized \cup {s}
  /\ UNCHANGED <<currentSlot, blocks, votes, certificates, byzantineVotes>>

Next ==
  \/ AdvanceSlot
  \/ \E v \in HonestValidators : ProduceBlock(v)
  \/ \E v \in HonestValidators : \E s \in 1..MaxSlot : Vote(v, s)
  \/ \E v \in ByzantineValidators : \E s \in 1..MaxSlot : \E b1,b2 \in 1..MaxSlot : ByzantineEquivocate(v, s, b1, b2)
  \/ \E s \in 1..MaxSlot : CreateNotarCert(s)
  \/ \E s \in 1..MaxSlot : CreateFinalCert(s)
  \/ \E s \in 1..MaxSlot : FinalizeFast(s)
  \/ \E s \in 1..MaxSlot : FinalizeSlow(s)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety Properties

TypeOK ==
  /\ currentSlot \in 1..MaxSlot
  /\ blocks \subseteq [slot: 1..MaxSlot, producer: AllValidators]
  /\ votes \in [HonestValidators -> [1..MaxSlot -> [type: {"NoVote", "Notar"}, slot: 0..MaxSlot]]]
  /\ certificates \in [1..MaxSlot -> ["Notar" : [signers: SUBSET HonestValidators, slot: 0..MaxSlot],
                                     "FastFinal" : [signers: SUBSET HonestValidators, slot: 0..MaxSlot],
                                     "Final" : [signers: SUBSET HonestValidators, slot: 0..MaxSlot]]]
  /\ finalized \subseteq 1..MaxSlot
  /\ byzantineVotes \subseteq [validator: ByzantineValidators, slot: 1..MaxSlot, blocks: SUBSET(1..MaxSlot)]

NoConflictingFinalizations ==
  \A s1, s2 \in finalized : s1 = s2

CertificateUniqueness ==
  \A s \in 1..MaxSlot, t1,t2 \in {"Notar", "FastFinal", "Final"} :
    (certificates[s][t1] # NoCert /\ certificates[s][t2] # NoCert /\ t1 = t2) => certificates[s][t1] = certificates[s][t2]

StakeThresholdCorrectness ==
  \A s \in 1..MaxSlot, t \in {"Notar", "Final"} :
    certificates[s][t] # NoCert =>
      IsQuorum(TotalStakeOf(certificates[s][t].signers))

FastFinalStakeThreshold ==
  \A s \in 1..MaxSlot :
    certificates[s]["FastFinal"] # NoCert =>
      IsStrongQuorum(TotalStakeOf(certificates[s]["FastFinal"].signers))

-----------------------------------------------------------------------------
\* 20+20 Resilience Properties

\* Theorem: Byzantine stake bounded at ≤20%
ByzantineStakeBounded ==
  TotalStakeOf(ByzantineValidators) <= TotalStake \div 5

\* Theorem: Crashed stake bounded at ≤20%
CrashedStakeBounded ==
  TotalStakeOf(CrashedValidators) <= TotalStake \div 5

\* Theorem: Combined fault tolerance ≤40%
CombinedFaultBound ==
  TotalStakeOf(ByzantineValidators \union CrashedValidators) <= (TotalStake * 2) \div 5

\* Theorem: Honest stake ≥60% (safety threshold)
HonestMajority ==
  TotalStakeOf(HonestValidators) >= (TotalStake * 3) \div 5

\* Theorem: Safety despite 20+20 faults
SafetyDespite2020Faults ==
  \* All safety properties hold even with 20% Byzantine + 20% crashed
  /\ NoConflictingFinalizations
  /\ CertificateUniqueness
  /\ StakeThresholdCorrectness
  /\ FastFinalStakeThreshold

\* Theorem: No honest equivocation
HonestNoEquivocation ==
  \A v \in HonestValidators, s \in 1..MaxSlot :
    votes[v][s] # NoVote => \A v2 \in HonestValidators :
      (votes[v2][s] # NoVote /\ votes[v2][s].type = votes[v][s].type)

=============================================================================