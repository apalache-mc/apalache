-------------------------- MODULE FoldExcept ----------------------------------
(*
 * This specification measures performance in the presence of an anti-pattern.
 *)

EXTENDS Integers, Apalache 

CONSTANT
    \* A fixed set of processes
    \*
    \* @type: Set(Str);
    Proc

VARIABLES
    \* Process clocks
    \*
    \* @type: Str -> Int;
    clocks,
    \* Drift between pairs of clocks
    \*
    \* @type: <<Str, Str>> -> Int;
    drift

Init ==
    /\ clocks \in [ Proc -> Nat ]
    /\ drift = [ <<p, q>> \in Proc \X Proc |-> clocks[p] - clocks[q] ]

\* Uniformly advance the clocks and update the drifts.
\* This is smart TLA+.
NextFast ==
    \E delta \in Nat \ { 0 }:
        /\ clocks' = [ p \in Proc |-> clocks[p] + delta ]
        /\ drift' = [ <<p, q>> \in Proc \X Proc |-> clocks'[p] - clocks'[q] ]

\* Uniformly advance the clocks and update the drifts.
\* Not very smart TLA+. More like a program.
NextSlow ==
    \E delta \in Nat \ { 0 }:
        /\  LET \* @type: (Str -> Int, Str) => (Str -> Int);
                IncrementInLoop(clk, p) ==
                [ clk EXCEPT ![p] = @ + delta ]
            IN
            clocks' = FoldSet(IncrementInLoop, clocks, Proc)
        /\  LET \* @type: (<<Str, Str>> -> Int, <<Str, Str>>)
                \*          => <<Str, Str>> -> Int;
                SubtractInLoop(dft, pair) ==
                LET p == pair[1]
                    q == pair[2]
                IN
                [ dft EXCEPT ![p, q] = clocks'[p] - clocks'[q] ]
            IN
            drift' = FoldSet(SubtractInLoop, drift, Proc \X Proc)

\* Check that the clock drifts do not change
DriftInv ==
    \A p, q \in Proc:
        drift'[p, q] = drift[p, q]

===============================================================================
