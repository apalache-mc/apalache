-------------------------------- MODULE test4 -------------------------------
(***************************************************************************)
(* This is a specification of the Paxos algorithm without explicit leaders *)
(* or learners.  It refines the spec in Voting                             *)
(***************************************************************************)
EXTENDS Integers


  (*************************************************************************)
  (* An unspecified value that is not a ballot number.                     *)
  (*************************************************************************)
  
(***************************************************************************)
(* This is a message-passing algorithm, so we begin by defining the set    *)
(* Message of all possible messages.  The messages are explained below     *)
(* with the actions that send them.                                        *)
(***************************************************************************)
Message ==      [bal : {1}]
           \cup [type : {"1b"}, acc : {1}, bal : {1}, 
                 mbal : {1} , mval : {1}]
============================================================================
