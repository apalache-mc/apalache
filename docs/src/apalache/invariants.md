# Invariants: state, action, and trace

Until recently, Apalache only supported checking of state invariants. A state
invariant is a predicate over state variables and constants. State invariants
are, by far, the most common ones. Recently, we have added support for action
invariants and trace invariants. [Action properties] were highlighted by Hillel
Wayne; they can be checked with action invariants. Trace invariants let us
reason about finite executions.


## State invariants

You have probably seen state invariants before. Consider the following specification.

```tla
{{#include ../../../test/tla/Invariants.tla:1:38}}
```

We let you guess what this specification is doing. As for its properties, it contains
two state invariants:

 * Predicate `StateInv` that states `Done \intersect In = {}`, and
 * Predicate `BuggyStateInv` that states `Done \subseteq In`.

We call these predicates state invariants, as we expect them to hold in
every state of an execution. To check, whether these invariants hold true,
we run Apalache as follows:

```sh
$ apalache check --inv=StateInv Invariants.tla
...
Checker reports no error up to computation length 10
...
$ apalache check --inv=BuggyStateInv Invariants.tla
...
State 1: state invariant 0 violated. Check the counterexample in: counterexample.tla, MC.out, counterexample.json
...
```

*The standard footprint: By default, Apalache checks executions of length up
to 10 steps.*

## Action invariants

Let's have a look at two other predicates in `Invariants.tla`:

```tla
{{#include ../../../test/tla/Invariants.tla:39:48}}
```

Can you see a difference between `ActionInv` & `BuggyActionInv` and `StateInv`
& `BuggyStateInv`?

You have probably noticed that `ActionInv` as well as `BuggyActionInv` use
unprimed variables and primed variables. So they let us reason about two
consecutive states of an execution. They are handy for checking specification
progress. Similar to state invariants, we can check, whether action invariants
hold true by running Apalache as follows:


```sh
$ apalache check --inv=ActionInv Invariants.tla
...
Checker reports no error up to computation length 10
...
$ apalache check --inv=BuggyActionInv Invariants.tla
...
State 0: action invariant 0 violated. Check the counterexample in: counterexample.tla, MC.out, counterexample.json
...
```

There is no typo in the CLI arguments above: You pass action invariants the same way
as you pass state invariants. Preprocessing in Apalache is clever enough to figure out,
what kind of invariant it is dealing with.

<a name="traceInv"></a>
## Trace invariants


Let's have a look at the following two predicates in `Invariants.tla`:

```tla
{{#include ../../../test/tla/Invariants.tla:49:62}}
```

These predicates are quite different from state invariants and action
invariants.  Both `TraceInv` and `BuggyTraceInv` accept the parameter `hist`,
which store the execution history as a sequence of records. Having the
execution history, you can check plenty of interesting properties. For
instance, you can check, whether the result of an execution somehow matches the
input values.


```sh
$ apalache check --inv=TraceInv Invariants.tla
...
Checker reports no error up to computation length 10
...
$ apalache check --inv=BuggyTraceInv Invariants.tla
...
State 3: trace invariant 0 violated. Check the counterexample in: counterexample.tla, MC.out, counterexample.json
...
```

Trace invariants are quite powerful. You can write down temporal properties as
trace invariants. However, we recommend to use trace invariants for testing, as
they are too powerful. For verification, you should use temporal properties.

[Action properties]: https://www.hillelwayne.com/post/action-properties/
