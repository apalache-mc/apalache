----------------------------- MODULE RecordExcept987 ------------------------
EXTENDS Integers

VARIABLES
    (*
      @typeAlias: R = [
         id: Str,
         name: Str,
         oneMoreField: Bool,
         age: Int,
         isShadow: Bool,
         isAllow: Bool
      ];
      @type: Set(R);
    *)
    recs,
    \* @type: Bool;
    ok

Init ==
  /\ ok = TRUE
  /\ recs = { }

Next ==
  /\ ok' = \A r \in recs:
        r.age < 15
  /\ \/ LET nr == [name |-> "foo",
                   age |-> 10,
                   isShadow |-> TRUE,
                   id |-> "111",
                   isAllow |-> FALSE,
                   oneMoreField |-> TRUE
                   ]
       IN
       recs' = recs \union { nr }
    \/ \E r \in recs:
        LET nr == [r EXCEPT !.age = @ + 1] IN
        /\ recs' = (recs \union {nr}) \ {r}
        /\ nr /= r
    \/ UNCHANGED recs

Inv ==
    \A r \in recs:
        r.age < 15

=============================================================================
