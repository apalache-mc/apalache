--------------------------- MODULE MC5_Prisoners ------------------------------
Prisoner == {
    "0_OF_PRISONER", "1_OF_PRISONER",
    "2_OF_PRISONER", "3_OF_PRISONER", "456_OF_PRISONER"
}

Counter == "456_OF_PRISONER"

VARIABLES 
  \* @type: Bool;
  switchAUp,
  \* @type: Bool;
  switchBUp,    
    (***********************************************************************)
    (* The states of the two switches, represented by boolean-valued       *)
    (* variables.                                                          *)
    (***********************************************************************)
    
  \* @type: PRISONER -> Int;
  timesSwitched,
    (***********************************************************************)
    (* For ever prisoner except the counter, timesSwitched[p] is the       *)
    (* number of times prisoner p has moved switch A up.  It is initially  *)
    (* 0 and will equal at most 2.                                         *)
    (***********************************************************************)

  \* @type: Int;
  count
    (***********************************************************************)
    (* The number of times the Counter has switched switch A down.         *)
    (***********************************************************************)

INSTANCE PrisonersTyped

\* use this invariant to find a solution
Inv == ~Done
===============================================================================
