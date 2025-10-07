--------------------------- MODULE PartitionAlpenglow -----------------------------
(*
  Network Partition Model of Alpenglow Consensus

  This specification models network partitions and recovery:
  - Temporary network splits that isolate validator subsets
  - Partition recovery and state synchronization
  - Verifies that consensus can recover from partitions

  Key Theorem: Alpenglow recovers from temporary network partitions
  and maintains consistency once partitions heal.
*)

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Validators,     \* Set of all validators
  MaxSlot,        \* Maximum slot number
  TotalStake      \* Total stake

VARIABLES
  currentSlot,    \* Current slot
  blocks,         \* Blocks produced
  votes,          \* Votes cast
  certificates,   \* Certificates
  finalized,      \* Finalized slots
  partitions,     \* Current network partitions: set of validator subsets
  partitionTimer  \* Timer for partition duration

vars == <<currentSlot, blocks, votes, certificates, finalized, partitions, partitionTimer>>

StakePerValidator == TotalStake \div Cardinality(Validators)
IsQuorum(stake) == stake >= ((TotalStake * 3) \div 5)
IsStrongQuorum(stake) == stake >= ((TotalStake * 4) \div 5)
TotalStakeOf(S) == Cardinality(S) * StakePerValidator

Init ==
  /\ currentSlot = 1
  /\ blocks = [s \in 1..MaxSlot |-> [slot |-> s, parent |-> IF s = 1 THEN 0 ELSE s-1]]
  /\ votes = [v \in Validators |-> [s \in 1..MaxSlot |-> NoVote]]
  /\ certificates = [s \in 1..MaxSlot |-> [type \in {"Notar", "FastFinal", "Final"} |-> NoCert]]
  /\ finalized = {}
  /\ partitions = {Validators}  \* Initially fully connected
  /\ partitionTimer = 0

NoVote == [type |-> "NoVote", slot |-> 0]
NoCert == [signers |-> {}, slot |-> 0]

\* Check if two validators can communicate (same partition)
CanCommunicate(v1, v2) ==
  \E partition \in partitions : v1 \in partition /\ v2 \in partition

\* Get validators in same partition as v
PartitionOf(v) == CHOOSE partition \in partitions : v \in partition

\* Create network partition
CreatePartition ==
  /\ Cardinality(partitions) = 1  \* Only partition if currently fully connected
  /\ LET partition1 == {"v1", "v2"}  \* Split into two partitions
         partition2 == Validators \ partition1
     IN /\ partitions' = {partition1, partition2}
        /\ partitionTimer' = 5  \* Partition lasts 5 steps
  /\ UNCHANGED <<currentSlot, blocks, votes, certificates, finalized>>

\* Heal network partition
HealPartition ==
  /\ Cardinality(partitions) > 1  \* Only heal if partitioned
  /\ partitionTimer > 0
  /\ partitionTimer' = partitionTimer - 1
  /\ IF partitionTimer' = 0
     THEN partitions' = {Validators}  \* Network heals
     ELSE UNCHANGED partitions
  /\ UNCHANGED <<currentSlot, blocks, votes, certificates, finalized>>

\* Advance slot (only if network is connected)
AdvanceSlot ==
  /\ Cardinality(partitions) = 1  \* Only advance when network is connected
  /\ currentSlot < MaxSlot
  /\ currentSlot' = currentSlot + 1
  /\ UNCHANGED <<blocks, votes, certificates, finalized, partitions, partitionTimer>>

\* Produce block (partition-aware)
ProduceBlock(v) ==
  /\ ~\E b \in blocks : b.slot = currentSlot /\ b.producer = v
  /\ blocks' = blocks \cup {[slot |-> currentSlot, producer |-> v]}
  /\ UNCHANGED <<currentSlot, votes, certificates, finalized, partitions, partitionTimer>>

\* Vote (only within partition)
Vote(v, s) ==
  /\ s < currentSlot
  /\ s \in 1..MaxSlot
  /\ \E b \in blocks : b.slot = s
  /\ votes[v][s] = NoVote
  /\ LET partitionValidators == PartitionOf(v)
         partitionVotes == {v2 \in partitionValidators : votes[v2][s] # NoVote}
         partitionStake == TotalStakeOf(partitionVotes \cup {v})
     IN /\ IsQuorum(partitionStake) \/ IsStrongQuorum(partitionStake)  \* Can form quorum in partition
        /\ votes' = [votes EXCEPT ![v][s] = [type |-> "Notar", slot |-> s]]
  /\ UNCHANGED <<currentSlot, blocks, certificates, finalized, partitions, partitionTimer>>

\* Create certificate (partition-aware quorum)
CreateNotarCert(s) ==
  /\ s < currentSlot
  /\ s \in 1..MaxSlot
  /\ certificates[s]["Notar"] = NoCert
  /\ LET allVoters == {v \in Validators : votes[v][s] # NoVote}
         voterPartitions == {PartitionOf(v) : v \in allVoters}
         \* Check if any partition has quorum
         hasPartitionQuorum == \E p \in voterPartitions :
           LET partitionVoters == {v \in allVoters : PartitionOf(v) = p}
           IN IsQuorum(TotalStakeOf(partitionVoters))
     IN /\ hasPartitionQuorum
        /\ certificates' = [certificates EXCEPT ![s]["Notar"] = [signers |-> allVoters, slot |-> s]]
  /\ UNCHANGED <<currentSlot, blocks, votes, finalized, partitions, partitionTimer>>

\* Finalize (only when network is healed)
FinalizeFast(s) ==
  /\ Cardinality(partitions) = 1  \* Only finalize when network is connected
  /\ certificates[s]["FastFinal"] # NoCert
  /\ s \notin finalized
  /\ finalized' = finalized \cup {s}
  /\ UNCHANGED <<currentSlot, blocks, votes, certificates, partitions, partitionTimer>>

FinalizeSlow(s) ==
  /\ Cardinality(partitions) = 1  \* Only finalize when network is connected
  /\ certificates[s]["Notar"] # NoCert
  /\ certificates[s]["Final"] # NoCert
  /\ s \notin finalized
  /\ finalized' = finalized \cup {s}
  /\ UNCHANGED <<currentSlot, blocks, votes, certificates, partitions, partitionTimer>>

Next ==
  \/ AdvanceSlot
  \/ \E v \in Validators : ProduceBlock(v)
  \/ \E v \in Validators : \E s \in 1..MaxSlot : Vote(v, s)
  \/ CreatePartition
  \/ HealPartition
  \/ \E s \in 1..MaxSlot : CreateNotarCert(s)
  \/ \E s \in 1..MaxSlot : FinalizeFast(s)
  \/ \E s \in 1..MaxSlot : FinalizeSlow(s)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety Properties

TypeOK ==
  /\ currentSlot \in 1..MaxSlot
  /\ partitions \subseteq SUBSET Validators
  /\ partitionTimer \in 0..10
  /\ \A p \in partitions : p # {}

NoConflictingFinalizations ==
  \A s1, s2 \in finalized : s1 = s2

PartitionConsistency ==
  \* Once network heals, all finalized blocks remain consistent
  Cardinality(partitions) = 1 => NoConflictingFinalizations

-----------------------------------------------------------------------------
\* Partition Recovery Properties

\* Theorem: Network eventually heals from partitions
NetworkEventuallyHeals ==
  <>[](Cardinality(partitions) = 1)

\* Theorem: Consensus eventually resumes after partition healing
ConsensusResumesAfterHealing ==
  []((Cardinality(partitions) > 1) => <>(Cardinality(partitions) = 1 /\ finalized # {}))

\* Theorem: No conflicting finalizations even during partitions
SafetyDuringPartitions ==
  []NoConflictingFinalizations

=============================================================================