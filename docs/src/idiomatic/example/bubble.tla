----------------------- MODULE bubble -----------------------------------------------
(* This is a simple specification of bubble sort.                             *)
(* WARNING: this specification is using the new type annotations of Apalache, *)
(*          which are not supported by the model checker yet.                 *)
EXTENDS Integers, Typing

\*CONSTANTS in_list
in_list == "Seq(Int)" ##
    <<5, 4, 3, 8, 1>>

VARIABLES my_list, finished

\* new type annotations in Apalache
TypeAssumptions1 ==
    /\ AssumeType(my_list, "Seq(Int)")
    /\ AssumeType(finished, "Bool")

Init ==
    /\ my_list = in_list
    /\ finished = FALSE

IsSorted(lst) == "Seq(Int) => Bool" ##
    \A i \in DOMAIN lst \ {1}:
        lst[i - 1] <= lst[i]

WhenSorted ==
    /\ IsSorted(my_list)
    /\ finished' = TRUE
    /\ UNCHANGED my_list

WhenUnsorted ==
    /\ \E i \in DOMAIN my_list \ {1}:
        /\ my_list[i - 1] > my_list[i]
        /\ my_list' = [my_list EXCEPT ![i - 1] = my_list[i],
                                      ![i] = my_list[i - 1]]
    /\ finished' = FALSE

Next ==
    IF finished
    THEN UNCHANGED <<my_list, finished>>
    ELSE WhenSorted \/ WhenUnsorted

Inv ==
    finished =>
      /\ IsSorted(my_list)

\* Apalache fails here, as it attempts to expand the set [indices -> indices]
Inv2 ==
    finished =>
      \* the sorting algorithm may change the order, but not the elements
      /\ LET indices == DOMAIN in_list IN
        \E reordering \in [indices -> indices]:
          \* index reordering covers all indices
          /\ indices = { reordering[i]: i \in indices }
          \* all elements of in_list are in the my_list, up to reordering
          /\ \A i \in indices:
              my_list[i] = in_list[reordering[i]]

=====================================================================================
