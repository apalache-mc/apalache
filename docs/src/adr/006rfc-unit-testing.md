# RFC-006: Unit testing and property-based testing of TLA+ specifications

| author      | revision |
| ----------- | --------:|
| Igor Konnov |        1 |

## 1. Long rationale

TLA+ is a specification language that was designed to be executable inside a
human brain. Moreover, it was intended to run in the brains that underwent a
specific software upgrade, called mathematical training. Many years have passed
since then. We now have automatic tools that can run TLA+ in a computer (to
some extent). Even more, these tools can prove or disprove certain properties
of TLA+ specs.

Nowadays, we have two tools when writing a TLA+ spec: our brain and a model
checker. Both these tools have the same problem. They are slow. Software
engineers are facing a similar problem when they are trying to test their
system against different inputs. Interestingly, software engineers have found a
way around this problem. They first test the individual parts of the system and
then they test the system as a whole. The former is done with unit tests,
whereas the latter is done with integration tests. (Software engineers probably
borrowed this approach from industrial engineers.) Unit tests are used almost
interactively, to debug a small part of the system, while integration tests are
run in a continuous integration environment, which is not interactive at all.

Actually, our brains also have a built-in ability of abstracting away from one
part of a problem while thinking about the other part. That is why some of us
can still win against automatic tools. Model checkers do not have this built-in
ability. So it looks like when we are using TLC or Apalache, we are doing
integration testing all the time. Unfortunately, when we are checking a
specification as a whole, we rarely get a quick response, except for very small
specs. This is hardly surprising, as we are interested in specifying complex
systems, not the trivial ones.

Why cannot we do something like [Unit testing][] in Apalache? We believe that
we actually can do that. We can probably do it even better by implementing
[Property-based testing][], that is, test parts of our specifications against a
large set of inputs instead of testing it against a few carefully crafted
inputs.

## 2. A motivating example

Let's consider a relatively simple distributed algorithm as an example.  The
repository of [TLA+ examples][] contains the well-known leader election
algorithm called [LCR][]. The algorithm is over 40 years old, but it is tricky
enough to be still interesting. To understand the algorithm, check [Distributed
Algorithms][] by Nancy Lynch.

As the description suggests, when we fix `N` to `6` and `Id` to
`<<27, 4, 42, 15, 63, 9>>`, TLC checks that the spec satisfies the invariant
`Correctness` in just 11 seconds, after having explored 40K states.
Of course, had we wanted to check the property for all possible combinations
of six unique identifiers in the range of `1..6`, we would had to run TLC
`6! = 720` times, which would take over 2 hours.

In Apalache, we can setup a TLA+ module instance, to check all instances of
the algorithm that have from 2 to 6 processes:

```tla
{{#include ../../../test/tla/ChangRobertsTyped_Test.tla:1:47}}
```

By running Apalache as follows, we can check `Correctness` for all
configurations of 2 to 6 processes and all combinations of `Id`:

```sh
apalache check --cinit=ConstInit \
  --init=InitAndAssumptions --inv=Correctness ChangRobertsTyped_Test.tla
```

Actually, we do not restrict `Id` to be a function from `1..N` to `1..N`, but
rather allow `Id` to be a function from `1..N` to `Int`. So Apalache should
be able to check an infinite number of configurations!

Unfortunately, Apalache starts to dramatically slow down after having explored
6 steps of the algorithm. Indeed, it does symbolic execution for a
non-deterministic algorithm and infinitely many inputs. We could try to improve
the SMT encoding, but that would only win us several steps more. A more
realistic approach would be to find an inductive invariant and let Apalache
check it.

It looks like we are trapped: Either we have to invest some time in
verification, or we can check the algorithm for a few data points. In case
of LCR, the choice of process identifiers is important, so it is not clear at
all, whether a few data points are giving us a good confidence.

This situation can be frustrating, especially when you are designing a large
protocol. For instance, both Apalache and TLC can run for hours on [Raft][]
without finishing. We should be able to quickly debug our specs like software
engineers do!


## 3. An approach to writing tests

*What we describe below has not been implemented yet. Apalache has all the
necessary ingredients for implementing this approach. We are asking for your
input to find an ergonomic approach to testing TLA+ specifications.*

A complete specification can be found in [ChangRobertsTyped_Test.tla][].

Our idea is to quickly check operators in isolation, without analyzing the
whole specification and without analyzing temporal behavior of the
specification. There are two principally different kinds of operators in TLA+:

 - Stateless operators that take input parameters and return the result.
    These operators are similar to functions in functional languages.

 - Action operators that act on a specification state.
    These operators are similar to procedures in imperative languages.

### 3.1. Testing stateless operators

Consider the following auxiliary operator in the specification:

```tla
{{#include ../../../test/tla/ChangRobertsTyped.tla:43:43}}
```

While this operator is defined in the specification, it is clear that it is
well isolated from the rest of the specification: We only have to know the
value of the constant `N` and the value of the operator parameter `n`.

```tla
{{#include ../../../test/tla/ChangRobertsTyped_Test.tla:50:58}}
```

This test is very simple. It requires `succ(n)` to be in the set `Node`, for
all values `n \in Node`. The body of the operator `Test_succ` is pure TLA+.
We annotate the operator with `@testStateless`, to indicate that it should
be checked in a stateless context.

We should be able to run this test via:

```sh
apalache test --cinit=ConstInit --include=Test_succ ChangRobertsTyped_Test.tla
```

We single out the test `Test_succ`, as we expect the `test` command to run all
tests by default. Also, we have to pass `--cinit=ConstInit` to initialize the
parameter `N`.


Alternatively, we could use the operator `Gen` from [Apalache.tla][] as follows:

```tla
{{#include ../../../test/tla/ChangRobertsTyped_Test.tla:60:67}}
```

In case of integers, a generator does not bring any additional value, but it
could be useful for generating a set or a function.

### 3.2. Testing actions

Testing stateless operators is nice. However, TLA+ is built around the concept
of a state machine. Hence, we believe that most of the testing activity will be
centered around TLA+ actions. For instance, the [LCR][] specification has two
actions: `n0` and `n1`. Let's have a look at `n0`:

```tla
{{#include ../../../test/tla/ChangRobertsTyped.tla:101:107}}
```

Assume we like to test it without looking at the rest of the system, namely,
the predicates `Init` and `n1`. First of all, we have to describe the states
that could be passed to the action `n0`:

```tla
{{#include ../../../test/tla/ChangRobertsTyped_Test.tla:71:84}}
```

In `Prepare_n0`, we let the solver to produce bounded data structures with
`Gen`, by providing bounds on the size of every set, function, sequence, etc.
Since we don't want to have completely arbitrary data structures, we further
restrict them with `TypeOK`, which we conveniently have in the specification.

Further, we specify what kind of outcome we expect:

```tla
{{#include ../../../test/tla/ChangRobertsTyped_Test.tla:86:89}}
```

(Do you think this condition actually holds true after firing `n0`?)

Finally, we have to specify, how to run the action `n0`. In fact, if you look
at `Next`, this requires us to write a bit of code, instead of just calling
`n0`:

```tla
{{#include ../../../test/tla/ChangRobertsTyped_Test.tla:91:101}}
```

The operator `Action_n0` carries several annotations:

 - The annotation `@testAction` indicates that `Action_n0` should be tested
    as an action that is an operator over unprimed and primed variable.
 - The annotation `@requre("Prepare_n0")` tells the framework that
    `Prepare_n0` should act as an initialization predicate for testing
    `Action_n0`.
 - The annotation `@ensure("Assert_n0")` tells the framework that
    `Assert_n0` should hold after `Action_n0` has been fired.

We should be able to run this test via:

```sh
apalache test --cinit=ConstInit --include=TestAction_n0 ChangRobertsTyped_Test.tla
```

As you can see, our test is written in the spirit of property-based testing.
We were inspired by the design [Scalatest] and [Scalacheck]. In comparison
to pure property-based testing, we have to decompose the test in three parts:

 - preparing the states (like in `Init`),
 - executing the action (like a single instance of `Next`),
 - testing the next states (like an invariant).

## 4. Using tests for producing quick examples

It is often nice to see examples of test inputs that pass the
test. Apalache has all the ingredients to do that that. We should be able
to run a command like that:

```sh
apalache example --cinit=ConstInit --include=TestAction_n0 ChangRobertsTyped_Test.tla
```

The above call would produce `exampla.tla`, a TLA+ description of two states
that satisfy the test. This is similar to `counterexample.tla`, which is
produced when an error is found.



[Unit testing]: https://en.wikipedia.org/wiki/Unit_testing
[Property-based testing]: https://en.wikipedia.org/wiki/QuickCheck
[TLA+ examples]: https://github.com/tlaplus/Examples/
[LCR]: https://github.com/tlaplus/Examples/tree/master/specifications/chang_roberts
[ChangRobertsTyped_Test.tla]: ../../../test/tla/ChangRobertsTyped_Test.tla
[Distributed Algorithms]: https://dl.acm.org/doi/book/10.5555/2821576
[Raft]: https://github.com/tlaplus/Examples/tree/master/specifications/raft
[Apalache.tla]: https://github.com/informalsystems/apalache/blob/80cf914fe7272b14832a47b21193f5dfe8119348/src/tla/Apalache.tla
[Scalacheck]: https://www.scalacheck.org/
[Scalatest]: https://www.scalatest.org/
