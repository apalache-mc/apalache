<a name="assignments"></a>
<a name="symbolicTransitions"></a>
## Assignments and symbolic transitions

Let us go back to the example
[`test/tla/y2k.tla`](https://github.com/informalsystems/apalache/blob/main/test/tla/y2k.tla)
and run `apalache-mc` against
[`test/tla/y2k_override.tla`](https://github.com/informalsystems/apalache/blob/main/test/tla/y2k_override.tla)
while instructing Apalache to write intermediate output files:

```console
$ apalache-mc check --write-intermediate=true y2k_override.tla
```

We can check the detailed output of the `TransitionFinderPass` in the file
`_apalache-out/y2k_override.tla/<timestamp>/intermediate/<pass>_OutTransitionFinderPass.tla`, where
`<timestamp>` looks like `2021-12-01T12-07-41_1998641578103809179`, and `<pass>` is a two-digit number like `08`:

```tla
{{#include ../../../../test/tla/y2k_09_OutTransition.tla::}}
```

As you can see, the model checker did two things:

1. It has translated several expressions that look like `x' = e` into `x' := e`.
   For instance, you can see `year' := 80` and `hasLicense' := FALSE` in
   `Init_si_0000`. We call these expressions **assignments**.
1. It has factored the operator `Next` into two operators `Next_si_0000` and `Next_si_0001`.
   We call these operators **symbolic transitions**.

Pure TLA+ does not have the notions of assignments and symbolic
transitions.  However, TLC sometimes treats expressions `x' = e` and `x' \in S`
as if they were assigning a value to the variable `x'`. TLC does so
dynamically, during the breadth-first search. Apalache looks statically for assignments
among the expressions `x' = e` and `x' \in S`.

When factoring out operators into symbolic transitions, Apalache splits the
action operators `Init` and `Next` into disjunctions (e.g., `A_0 \/ ... \/ A_n`),
represented in the concrete syntax as a sequence of operator definitions of the
form

``` tla
A$0 == ...
...
A$n == ...
```

The main contract between the assignments and symbolic transitions is as
follows:

> For every variable `x` declared with `VARIABLE`, there is exactly one
> assignment of the form `x' := e` in every symbolic transition `A_n`.

If Apalache cannot find expressions with the above properties, it fails.
Consider the example
[`test/tla/Assignments20200309.tla`](https://github.com/informalsystems/apalache/blob/main/test/tla/Assignments20200309.tla):

```tla
{{#include ../../../../test/tla/Assignments20200309.tla::}}
```

Run the checker with:

```bash
apalache-mc check Assignments20200309.tla
```

Apalache reports an error as follows:

```console
...
PASS #9: TransitionFinderPass
To understand the error, [check the
manual](https://apalache.informal.systems/docs/apalache/principles/assignments.html):
Assignment error: No assignments found for: a
It took me 0 days  0 hours  0 min  1 sec
Total time: 1.88 sec
EXITCODE: ERROR (255)
```

### More details

**Check [Assignments and Symbolic Transitions in
Depth](../assignments-in-depth.md).**

