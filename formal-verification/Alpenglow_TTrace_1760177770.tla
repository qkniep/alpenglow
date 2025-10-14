---- MODULE Alpenglow_TTrace_1760177770 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, Alpenglow

_expression ==
    LET Alpenglow_TEExpression == INSTANCE Alpenglow_TEExpression
    IN Alpenglow_TEExpression!expression
----

_trace ==
    LET Alpenglow_TETrace == INSTANCE Alpenglow_TETrace
    IN Alpenglow_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        finalized = ({})
        /\
        currentSlot = (4)
        /\
        certificates = (<<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>)
        /\
        blocks = (<<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>)
        /\
        votes = ([v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v3 |-> <<[type |-> "Final", slot |-> 1], [type |-> "Final", slot |-> 2], [type |-> "Final", slot |-> 3]>>, v4 |-> <<[type |-> "Final", slot |-> 1], [type |-> "Final", slot |-> 2], [type |-> "Final", slot |-> 3]>>])
    )
----

_init ==
    /\ currentSlot = _TETrace[1].currentSlot
    /\ finalized = _TETrace[1].finalized
    /\ blocks = _TETrace[1].blocks
    /\ certificates = _TETrace[1].certificates
    /\ votes = _TETrace[1].votes
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ currentSlot  = _TETrace[i].currentSlot
        /\ currentSlot' = _TETrace[j].currentSlot
        /\ finalized  = _TETrace[i].finalized
        /\ finalized' = _TETrace[j].finalized
        /\ blocks  = _TETrace[i].blocks
        /\ blocks' = _TETrace[j].blocks
        /\ certificates  = _TETrace[i].certificates
        /\ certificates' = _TETrace[j].certificates
        /\ votes  = _TETrace[i].votes
        /\ votes' = _TETrace[j].votes

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("Alpenglow_TTrace_1760177770.json", _TETrace)

=============================================================================

 Note that you can extract this module `Alpenglow_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `Alpenglow_TEExpression.tla` file takes precedence 
  over the module `Alpenglow_TEExpression` below).

---- MODULE Alpenglow_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, Alpenglow

expression == 
    [
        \* To hide variables of the `Alpenglow` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        currentSlot |-> currentSlot
        ,finalized |-> finalized
        ,blocks |-> blocks
        ,certificates |-> certificates
        ,votes |-> votes
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_currentSlotUnchanged |-> currentSlot = currentSlot'
        
        \* Format the `currentSlot` variable as Json value.
        \* ,_currentSlotJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(currentSlot)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_currentSlotModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].currentSlot # _TETrace[s-1].currentSlot
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE Alpenglow_TETrace ----
\*EXTENDS IOUtils, TLC, Alpenglow
\*
\*trace == IODeserialize("Alpenglow_TTrace_1760177770.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE Alpenglow_TETrace ----
EXTENDS TLC, Alpenglow

trace == 
    <<
    ([finalized |-> {},currentSlot |-> 1,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v2 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v3 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 2,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v2 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v3 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 3,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v2 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v3 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v2 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v3 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v2 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v3 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v3 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "NoVote", slot |-> 0]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v3 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "NoVote", slot |-> 0]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "NoVote", slot |-> 0]>>, v3 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "NoVote", slot |-> 0]>>, v3 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v3 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v3 |-> <<[type |-> "Final", slot |-> 1], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v3 |-> <<[type |-> "Final", slot |-> 1], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "Final", slot |-> 1], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v3 |-> <<[type |-> "Final", slot |-> 1], [type |-> "Final", slot |-> 2], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "Final", slot |-> 1], [type |-> "NoVote", slot |-> 0], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v3 |-> <<[type |-> "Final", slot |-> 1], [type |-> "Final", slot |-> 2], [type |-> "NoVote", slot |-> 0]>>, v4 |-> <<[type |-> "Final", slot |-> 1], [type |-> "Final", slot |-> 2], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v3 |-> <<[type |-> "Final", slot |-> 1], [type |-> "Final", slot |-> 2], [type |-> "Final", slot |-> 3]>>, v4 |-> <<[type |-> "Final", slot |-> 1], [type |-> "Final", slot |-> 2], [type |-> "NoVote", slot |-> 0]>>]]),
    ([finalized |-> {},currentSlot |-> 4,certificates |-> <<[Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]], [Notar |-> [slot |-> 0, signers |-> {}], FastFinal |-> [slot |-> 0, signers |-> {}], Final |-> [slot |-> 0, signers |-> {}]]>>,blocks |-> <<[slot |-> 1, parent |-> 0], [slot |-> 2, parent |-> 1], [slot |-> 3, parent |-> 2]>>,votes |-> [v1 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v2 |-> <<[type |-> "Notar", slot |-> 1], [type |-> "Notar", slot |-> 2], [type |-> "Notar", slot |-> 3]>>, v3 |-> <<[type |-> "Final", slot |-> 1], [type |-> "Final", slot |-> 2], [type |-> "Final", slot |-> 3]>>, v4 |-> <<[type |-> "Final", slot |-> 1], [type |-> "Final", slot |-> 2], [type |-> "Final", slot |-> 3]>>]])
    >>
----


=============================================================================

---- CONFIG Alpenglow_TTrace_1760177770 ----
CONSTANTS
    Validators = { "v1" , "v2" , "v3" , "v4" }
    MaxSlot = 3
    TotalStake = 100

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Sat Oct 11 15:46:29 IST 2025