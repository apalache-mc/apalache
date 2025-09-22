---- MODULE Verifier_functionComparison ----
\* Test for function comparison involving a funcion with an empty domain
\* See https://github.com/apalache-mc/apalache/issues/1811
EXTENDS Apalache, Integers

VARIABLES
  \* @type: (Seq(Str) -> <<Str>>);
  result,
  \* @type: Bool;
  found

Init ==
  /\ result \in {[x \in {<<"s1">>} |-> <<"s2">>]}
  /\ result = [x \in {} |-> <<"s3">>]
  /\ found \in BOOLEAN

 Next ==
   UNCHANGED <<result, found>>

 NotFound ==
   ~found
====
