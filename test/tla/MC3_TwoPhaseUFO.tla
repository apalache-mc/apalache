------------------------ MODULE MC3_TwoPhaseUFO -------------------------------
\* a fixed instance of TwoPhaseUFO to be checked with Apalache or TLC

Values_RM == { "uval_SORT_RM_r1", "uval_SORT_RM_r2", "uval_SORT_RM_r3" }

VARIABLES
  \* rmState[rm] is the state of resource manager RM.
  \* It is an uninterpreted non-Boolean function, which is fine in UFOL.
  \* @type: SORT_RM -> SORT_STATE;
  rmState,
  \* The state of the transaction manager.
  \* It is simply an uninterpreted constant.
  \* @type: SORT_STATE;
  tmState,       \* The state of the transaction manager.
  \* The set of RMs from which the TM has received 'Prepared'
  \* messages, which is expressed as a predicate in UFOL.
  \* @type: SORT_RM -> Bool;
  tmPrepared,    
  \* Three predicates, one per message type.
  \* In contrast to the original specification, we have to partition
  \* message types into three subsets, which are modelled as predicates.

  \* messages of the type 'Prepared'
  \* @type: SORT_RM -> Bool;
  msgsPrepared,
  \* messages of the type 'Commit'
  \* @type: Bool;
  msgsCommit,
  \* messages of the type 'Abort'
  \* @type: Bool;
  msgsAbort

INSTANCE TwoPhaseUFO

===============================================================================
