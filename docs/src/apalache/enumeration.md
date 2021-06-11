# Enumerating counterexamples

By default, Apalache stops whenever it finds a property violation. This is true
for the commands that are explained in the Section on [Running the
Tool](./running.md). Sometimes, we want to produce multiple counterexamples;
for instance, to generate multiple tests.

Consider the following TLA+ specification:

```tla
{{#include ../../../test/tla/View2.tla:1:24}}
```

We can run Apalache to check the state invariant `Inv`:

```sh
$ apalache check --inv=Inv View2.tla
```

Apalache quickly finds a counterexample that looks like this:

```tla
...
(* Initial state *)
State0 == x = 0

(* Transition 0 to State1 *)
State1 == x = 1
...
```

**Producing multiple counterexamples.**
If we want to see more examples of invariant violation, we can ask Apalache to
produce up to 50 counterexamples:

```sh
$ apalache check --inv=Inv --max-error=50 View2.tla
...
Found 20 error(s)
...
```

Whenever the model checker finds an invariant violation, it reports a
counterexample to the current symbolic execution and proceeds with the next action.
For instance, if the symbolic execution `Init \cdot A \cdot A` has a concrete
execution that violates the invariant `Inv`, the model checker would print this
execution and proceed with the symbolic execution `Init \cdot A \cdot B`.  That
is why the model checker stops after producing 20 counterexamples.

The option `--max-error` is similar to the option `--continue` in TLC, see [TLC
options][]. However, the space of counterexamples in Apalache may be infinite,
e.g., when we have integer variables, so `--max-error` requires an upper bound
on the number of counterexamples.

**Partitioning counterexamples with view abstraction.**
Some of the produced counterexamples are not really interesting. For
instance, `counterexample5.tla` looks like follows:

```tla
(* Initial state *)
State0 == x = 0

(* Transition 1 to State1 *)
State1 == x = -1

(* Transition 1 to State2 *)
State2 == x = -2

(* Transition 0 to State3 *)
State3 == x = -1
```

Obviously, the invariant is violated in `State1` already, so states `State2`
and `State3` are not informative. We could write a [trace
invariant](./invariants.md#traceInv) to enforce invariant violation only in the
last state. Alternatively, the model checker could enforce the constraint that
the invariant holds true in the intermediate states. As invariants usually
produce complex constraints and slow down the model checker, we leave the
choice to the user.

Usually, the specification author has a good idea of how to partition states
into interesting equivalence classes. We let you specify this partitiong by declaring
a view abstraction, similar to the `VIEW` configuration option in TLC.
Basically, two states are considered to be similar, if they have the same view.

In our example, we compute the state view with the operator `View1`:

```tla
{{#include ../../../test/tla/View2.tla:25:27}}
```

Hence, the states with `x = 1` and `x = 25` are similar, because their view has the
same value `<<FALSE, TRUE>>`. We can also define the view of an execution, simply
as a sequence of views of the execution states.

Now we can ask Apalache to produce up to 50 counterexamples again. This time we
tell it to avoid the executions that start with the view of an execution that
produced an error earlier:

```sh
$ apalache check --inv=Inv --max-error=50 --view=View1 View2.tla
...
Found 20 error(s)
...
```

Now `counterexample5.tla` is more informative:

```tla
(* Initial state *)
State0 == x = 0

(* Transition 2 to State1 *)
State1 == x = 0

(* Transition 2 to State2 *)
State2 == x = 0

(* Transition 0 to State3 *)
State3 == x = 1
```

Moreover, `counterexample6.tla` is intuitively a mirror version of `counterexample5.tla`:

```tla
(* Initial state *)
State0 == x = 0

(* Transition 2 to State1 *)
State1 == x = 0

(* Transition 2 to State2 *)
State2 == x = 0

(* Transition 0 to State3 *)
State3 == x = -1
```

By the choice of the view, we have partitioned the states into three
equivalence classes: `x < 0`, `x = 0`, and `x > 0`. It is often useful to write
a view as a tuple of predicates. However, you can write arbitrary TLA+ expressions.
A view is just a mapping from state variables to the set of values that can be
computed by the view expressions.

We are using this technique in model-based testing.  If you have found another
interesting application of this technique, please let us know!


[TLC options]: https://lamport.azurewebsites.net/tla/tlc-options.html?back-link=tools.html

