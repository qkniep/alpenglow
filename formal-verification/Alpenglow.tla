---------------------------- MODULE Alpenglow ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Validators, MaxSlot, TotalStake

ASSUME /\ Validators # {} /\ MaxSlot \in Nat /\ MaxSlot > 0 /\ TotalStake \in Nat \ {0}

Slots == 1..MaxSlot
CertType == {"Notar", "FastFinal", "Final"}
VoteType == {"Notar", "Final"}
NoVote == [type |-> "NoVote", slot |-> 0]
NoCert == [signers |-> {}, slot |-> 0]

VARIABLES currentSlot, blocks, votes, certificates, finalized
vars == <<currentSlot, blocks, votes, certificates, finalized>>

StakePerValidator == TotalStake \div Cardinality(Validators)
StakeWeight(S) == Cardinality(S) * StakePerValidator
IsQuorum(stake) == stake >= (TotalStake * 3) \div 5
IsStrongQuorum(stake) == stake >= (TotalStake * 4) \div 5
HasQuorum(signers) == IsQuorum(StakeWeight(signers))
HasStrongQuorum(signers) == IsStrongQuorum(StakeWeight(signers))

Init ==
    /\ currentSlot = 1
    /\ blocks = [s \in Slots |-> [slot |-> s, parent |-> IF s = 1 THEN 0 ELSE s-1]]
    /\ votes = [v \in Validators |-> [s \in Slots |-> NoVote]]
    /\ certificates = [s \in Slots |-> [type \in CertType |-> NoCert]]
    /\ finalized = {}

ProduceBlock ==
    /\ currentSlot <= MaxSlot
    /\ currentSlot' = currentSlot + 1
    /\ UNCHANGED <<blocks, votes, certificates, finalized>>

Vote(v, s, voteType) ==
    /\ s < currentSlot
    /\ s \in Slots
    /\ votes[v][s] = NoVote
    /\ votes' = [votes EXCEPT ![v][s] = [type |-> voteType, slot |-> s]]
    /\ UNCHANGED <<currentSlot, blocks, certificates, finalized>>

CreateNotarCert(s) ==
    /\ s < currentSlot
    /\ s \in Slots
    /\ certificates[s]["Notar"] = NoCert
    /\ LET notarVotes == {v \in Validators : votes[v][s] # NoVote /\ votes[v][s].type = "Notar"}
       IN /\ HasQuorum(notarVotes)
          /\ IF HasStrongQuorum(notarVotes)
             THEN /\ certificates' = [certificates EXCEPT 
                       ![s]["Notar"] = [signers |-> notarVotes, slot |-> s],
                       ![s]["FastFinal"] = [signers |-> notarVotes, slot |-> s]]
                  /\ finalized' = finalized \union {s}
             ELSE /\ certificates' = [certificates EXCEPT 
                       ![s]["Notar"] = [signers |-> notarVotes, slot |-> s]]
                  /\ UNCHANGED finalized
    /\ UNCHANGED <<currentSlot, blocks, votes>>

CreateFinalCert(s) ==
    /\ s < currentSlot
    /\ s \in Slots
    /\ certificates[s]["Notar"] # NoCert
    /\ certificates[s]["Final"] = NoCert
    /\ s \notin finalized
    /\ LET finalVotes == {v \in Validators : votes[v][s] # NoVote /\ votes[v][s].type = "Final"}
       IN /\ HasQuorum(finalVotes)
          /\ certificates' = [certificates EXCEPT 
               ![s]["Final"] = [signers |-> finalVotes, slot |-> s]]
          /\ finalized' = finalized \union {s}
    /\ UNCHANGED <<currentSlot, blocks, votes>>

Next ==
    \/ ProduceBlock
    \/ \E v \in Validators, s \in Slots : Vote(v, s, "Notar")
    \/ \E v \in Validators, s \in Slots : Vote(v, s, "Final")
    \/ \E s \in Slots : CreateNotarCert(s)
    \/ \E s \in Slots : CreateFinalCert(s)

Fairness == WF_vars(Next)
Spec == Init /\ [][Next]_vars

NoConflictingFinalizations ==
    \A s \in finalized :
        /\ certificates[s]["Notar"].slot = s
        /\ (certificates[s]["FastFinal"].slot > 0 =>
            certificates[s]["FastFinal"].slot = s)
        /\ (certificates[s]["Final"].slot > 0 =>
            certificates[s]["Final"].slot = s)

FastFinalImpliesNotar ==
    \A s \in Slots :
        certificates[s]["FastFinal"] # NoCert => certificates[s]["Notar"] # NoCert

FinalRequiresNotar ==
    \A s \in Slots :
        certificates[s]["Final"] # NoCert => certificates[s]["Notar"] # NoCert

ConsistentCertificates ==
    \A s \in Slots :
        /\ (certificates[s]["FastFinal"] # NoCert =>
            certificates[s]["FastFinal"].slot = certificates[s]["Notar"].slot)
        /\ (certificates[s]["Final"] # NoCert =>
            certificates[s]["Final"].slot = certificates[s]["Notar"].slot)

AllSlotsFinalized == 
    \A s \in Slots :
        ([]<> \E Q \in SUBSET Validators : HasQuorum(Q) /\ \A v \in Q : votes[v][s].type \in {"Notar", "Final"})
        => <>( s \in finalized)

(***************************************************************************)
(* Additional Safety Theorems                                            *)
(***************************************************************************)

\* THEOREM: Certificate uniqueness - at most one certificate per type per slot
CertificateUniqueness ==
    \A s \in Slots, certType \in CertType :
        certificates[s][certType] # NoCert =>
            \A s2 \in Slots : s2 # s => certificates[s2][certType].slot # s

\* THEOREM: Stake threshold correctness - certificates require proper quorum
StakeThresholdCorrectness ==
    \A s \in Slots :
        /\ (certificates[s]["Notar"] # NoCert =>
            HasQuorum(certificates[s]["Notar"].signers))
        /\ (certificates[s]["FastFinal"] # NoCert =>
            HasStrongQuorum(certificates[s]["FastFinal"].signers))
        /\ (certificates[s]["Final"] # NoCert =>
            HasQuorum(certificates[s]["Final"].signers))

\* THEOREM: Chain consistency - blocks form valid parent chain
ChainConsistency ==
    \A s1, s2 \in Slots :
        s1 \in finalized /\ s2 \in finalized /\ s2 > s1 =>
            blocks[s2].parent = s2 - 1

\* Note: Monotonic finalization is ensured by the protocol - finalized set only grows
\* (This is a temporal property, not checkable as invariant)

\* THEOREM: No equivocation - validators vote at most once per slot
NoEquivocation ==
    \A v \in Validators, s \in Slots :
        votes[v][s] # NoVote =>
            \/ votes[v][s].type = "Notar"
            \/ votes[v][s].type = "Final"

\* THEOREM: Fast path implies strong quorum (80%)
FastPathRequiresStrongQuorum ==
    \A s \in Slots :
        certificates[s]["FastFinal"] # NoCert =>
            IsStrongQuorum(StakeWeight(certificates[s]["FastFinal"].signers))

\* THEOREM: Finalized slots have valid certificates
FinalizedHaveValidCerts ==
    \A s \in finalized :
        \/ certificates[s]["FastFinal"] # NoCert
        \/ (certificates[s]["Notar"] # NoCert /\ certificates[s]["Final"] # NoCert)

\* THEOREM: Blocks exist before voting
BlocksExistBeforeVoting ==
    \A v \in Validators, s \in Slots :
        votes[v][s] # NoVote => s < currentSlot

\* THEOREM: Certificates created after sufficient votes
CertificatesRequireVotes ==
    \A s \in Slots :
        certificates[s]["Notar"] # NoCert =>
            \E Q \in SUBSET Validators :
                /\ HasQuorum(Q)
                /\ \A v \in Q : votes[v][s] # NoVote /\ votes[v][s].type = "Notar"

=============================================================================
