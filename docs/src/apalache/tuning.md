Parameters for fine tuning
==========================

The parameters for fine tuning can be passed to the checker in a properties
file.  Its name is given with the command-line option `--tuning-options-file=my.properties`.
This file supports variable substitution, e.g., `${x}` is replaced with the
value of `x`, if it was previously declared.

Alternatively, you can pass the tuning options right in the command-line by
passing the option `--tuning-options` that has the following format:

    ```
    --tuning-options=key1=val1
    --tuning-options=key1=val1:key2=val2
    ...
    ```

The following options are supported:

## Randomization

`smt.randomSeed=<int>` passes the random seed to `z3` (via `z3`'s parameters
`sat.random_seed` and `smt.random_seed`).

##  Timeouts

`search.smt.timeout=<seconds>` defines the timeout to the SMT solver in seconds.
The default value is `0`, which stands for the unbounded timeout.  For instance,
the timeout is used in the following cases: checking if a transition is enabled,
checking an invariant, checking for deadlocks. If the solver times out, it
reports 'UNKNOWN', and the model checker reports a runtime error.

## Invariant mode

`search.invariant.mode=(before|after)` defines the moment when the invariant is
checked. In the `after` mode, all transitions are first translated, one of them
is picked non-deterministically and then the invariant is checked. Although this
mode reduces the number of SMT queries, it usually requires more memory than the
`before` mode. In the `before` mode, the invariant is checked for every enabled
transition independently. The `before` mode may drastically reduce memory
consumption, but it may take longer than the `after` mode, provided that
Apalache has enough memory. The default mode is `before`.

## Guided search

### Preliminaries

In the following, step 0 corresponds to the initialization with ``Init``, step 1 is the first step with ``Next``, etc.

### Transition filter

`search.transitionFilter=<regex>`. Restrict the choice of symbolic transitions
at every step with a regular expression. The regular expression should recognize
words of the form `s->t`, where `s` is a step number and `t` is a transition
number.

For instance,
`search.transitionFilter=(0->0|1->5|2->(2|3)|[3-9]->.*|[1-9][0-9]+->.*)`
requires to start with the 0th transition, continue with the 5th transition,
then execute either the 2nd or the 3rd transition and after that execute
arbitrary transitions until the `length.`

Note that there is no direct correspondence between the transition numbers and
the actions in the TLA+ spec. To find the numbers, run Apalache with
`--write-intermediate=true` and check the transition numbers in
`_apalache-out/<MySpec>.tla/*/intermediate/XX_OutTransitionFinderPass.tla`: the
0th transition is called `Next_si_0000`, the 1st transition is called
`Next_si_0001`, etc.

### Invariant filter

`search.invariantFilter=<regex>`. Check the invariant only at the steps that
satisfy the regular expression. The regular expression should recognize words of
the form `s->ki`, where `s` is a step number, `k` is an invariant kind (["state"
or "action"][invariants]), and `i` is an invariant number.

For instance, `search.invariantFilter=10->.*|15->state0|20->action1` tells the
model checker to check

* all invariants only *after* exactly 10 steps have been made,
* the *first* state invariant only after exactly 15 steps, and
* the *second* action invariant after exactly 20 steps.

[Trace invariants][] are checked regardless of this filter.

Note that there is no direct correspondence between invariant numbers and the
operators in a TLA+ spec. Rather, the numbers refer to *verification conditions*
(i.e., broken up parts of a TLA+ invariant operator). To find these numbers, run
Apalache with `--write-intermediate=true` and check the invariant numbers in
`_apalache-out/<MySpec>.tla/*/intermediate/XX_OutVCGen.tla`. The 0th state
invariant is called `VCInv_si_0`, the 1st state invariant is called
`VCInv_si_1`, and so on. For action invariants, the declarations are named
`VCActionInv_si_0`, `VCActionInv_si_1` etc.

This option is useful, e.g., for checking consensus algorithms,
where the decision cannot be revoked. So instead of checking the invariant
after each step, we can do that after the algorithm has made a good number of
steps.
You can also use this option to check different parts of an invariant on
different machines to speed up turnaround time.

## Translation to SMT

### Short circuiting

`rewriter.shortCircuit=(false|true)`. When `rewriter.shortCircuit=true`, `A \/
B` and `A /\ B` are translated to SMT as if-then-else expressions, e.g., `(ite A
true B)`. Otherwise, disjunctions and conjunctions are directly translated to
`(or ...)` and `(and ...)` respectively. By default,
`rewriter.shortCircuit=false`.


[invariants]: ../apalache/principles/invariants.md
[trace invariants]: ../apalache/principles/invariants.md#trace-invariants
