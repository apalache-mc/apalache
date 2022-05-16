---------------------------- MODULE Solver ------------------------------------
(*
 * An abstract model of a constraint solver:
 *
 * 1. The states are represented with integers.
 *
 * 2. The constraints are represented with sets of integers (predicates) and
 * sets of pairs of integers (relations).
 *
 * Igor Konnov, Informal Systems, 2022
 *)

EXTENDS Integers, Sequences, Solver_typedefs

CONSTANTS
    \* The set of all potential states.
    \*
    \* @type: Set(Int);
    STATES

(*
 * context.unary contains constraints over states that are layered by time
 * frames.  Every set S of integers in unary is understood as a predicate
 * that evaluates to true on the elements of the set.
 *
 * context.binary contains constraints over pairs of states that are
 * layered by time frames. Every set R of integer pairs in binary is
 * understood as a predicate that evaluates to true on the elements of the
 * set.
 *
 * @type: (CONTEXT, Seq(Int)) => Bool;
 *)
IsModel(ctx, trace) ==
    /\  \A i \in DOMAIN trace:
          \A Pred \in ctx.unary[i]:
            trace[i] \in Pred
    /\  \A i \in DOMAIN trace \ { 1 }:
          \A Relation \in ctx.binary[i]:
            <<trace[i - 1], trace[i]>> \in Relation

\* @type: CONTEXT;
ContextEmpty ==
    [ unary |-> <<>>, binary |-> <<>> ]

\* @type: (CONTEXT, Set(Set(Int)), Set(Set(<<Int, Int>>))) => CONTEXT;
ContextPush(ctx, predicates, relations) ==
    [ unary |-> Append(ctx.unary, predicates),
      binary |-> Append(ctx.binary, relations) ]

\* @type: (CONTEXT, Set(Int)) => CONTEXT;
InsertPred(ctx, cons) ==
    [ ctx EXCEPT !.unary[Len(ctx.unary)] = @ \union { cons } ]

===============================================================================
