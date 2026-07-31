---------------------------- MODULE Bug3274 --------------------------
\* Regression test for https://github.com/apalache-mc/apalache/issues/3274:
\* TLCGet/TLCSet must accept both string (named) and integer (numbered) registers.
EXTENDS Integers, TLC

\* @type: () => Bool;
Foo ==
    /\ TLCSet(1, 42)
    /\ TLCSet("level", 7)
    /\ TLCGet(1) = TLCGet("level")
=================================================================
