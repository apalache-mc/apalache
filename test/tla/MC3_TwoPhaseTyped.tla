---------------------------- MODULE MC3_TwoPhaseTyped -------------------------

RM == { "0_OF_RM", "1_OF_RM", "2_OF_RM" }

VARIABLES
  \* @type: RM -> Str;
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  \* @type: Str;
  tmState,       \* The state of the transaction manager.
  \* @type: Set(RM);
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
  \* @type: Set($message);
  msgs

INSTANCE TwoPhaseTyped

\* Count the number of replicas that map to a value (Parikh image).
\* @type: (RM -> a) => (a -> Int);
CountImg(f) ==
    LET V == {f[id]: id \in RM} IN
    [ v \in V |-> Cardinality({ id \in RM: f[id] = v })]


View == <<
    CountImg(rmState),
    tmState
>>

\* find an example of TM aborting
TMAbortedEx ==
    tmState /= "aborted"

\* find an example of TM committing
TMCommittedEx ==
    tmState /= "committed"

\* find an example of all RMs aborted
RMAllAbortedEx ==
    ~(\A rm \in RM: rmState[rm] = "aborted")

\* find an example of all RMs committing
RMAllCommittedEx ==
    ~(\A rm \in RM: rmState[rm] = "committed")
===============================================================================
