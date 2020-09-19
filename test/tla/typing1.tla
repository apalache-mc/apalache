------------------------ MODULE typing1 ---------------------
\* Testing the Apalache type checker (ETC).
\* A simple specification that has a bit of type annotations.

EXTENDS Sequences, Typing

CONSTANT N, Base
VARIABLE x, seq

\* The assumptions about the parameters and variables.
\* The type checker cannot guess them, so we have to declare them.
LOCAL TypeAssumptions ==
  /\ AssumeType(N, "Int")
  /\ AssumeType(Base, "Set(ID)")
  /\ AssumeType(x, "ID")
  /\ AssumeType(seq, "Seq(ID)")

TrickyTypes ==
  /\ \E z \in {}: z = {}
  /\ [z \in {} |-> 1] = [z \in {} |-> 2]
  /\ \E z \in {<< >>}:
        TRUE

Mem(e, es) == "(a, Seq(a)) => Bool" :>
  (e \in {es[i]: i \in DOMAIN es})

\* No need for type annotation. It is pretty trivial.
Init ==
  /\ \E y \in Base:
        x' = y
  /\ seq' = << >>

\* this type is pretty trivial too.
Next ==
  \E y \in Base:
     /\ ~Mem(y, seq)
     /\ x' = y
     /\ seq' = Append(seq, x)

Inv ==
    ~Mem(x, seq)

==============================================================
