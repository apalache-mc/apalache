# Tutorial on checking PlusCal specifications with Apalache

**Difficulty: Blue trail – Easy**

In this short tutorial, we show how to annotate a [PlusCal specification][] of
the Bakery algorithm, to check it with Apalache. In particular, we check mutual
exclusion by _bounded model checking_ (which considers only bounded executions).
Moreover, we automatically prove mutual exclusion for unbounded executions by
_induction_.

We only focus on the part
related to Apalache. If you want to understand the Bakery algorithm and its
specification, check the comments in the original [PlusCal specification][].

## Setup

We assume that you have Apalache installed. If not, check the manual page on
[Apalache installation][]. The minimal required version is 0.22.0.

We provide all source files referenced in this tutorial as a [ZIP archive][]
download. We still recommend that you follow along typing the TLA+ examples
yourself.

## Running example: Bakery

We start with the [PlusCal specification][] of the [Bakery algorithm][]. This
specification has been checked with the model checker [TLC][].  Moreover,
[Leslie Lamport][] has proved safety of this algorithm with the [TLAPS][].


## Step 0: Remove the TLAPS proof

Since we are not interested in the TLAPS proof, we copy [Bakery.tla][] to
[BakeryWoTlaps.tla][] and modify it as follows:

 - Remove `TLAPS` from the list of extended modules

    ```tla
    EXTENDS Naturals
    ```

 - Remove the theorem and its proof:

    ```tla
    THEOREM Spec => []MutualExclusion
    ...
    ```

## Step 1: Add a module with type annotations

Let us check the types of [BakeryWoTlaps.tla][] with Apalache:

```sh
$ apalache-mc typecheck BakeryWoTlaps.tla
...
Typing input error: Expected a type annotation for VARIABLE max
```

The type checker complains about missing type annotations. See the [Tutorial on
Snowcat][] for details. When we try to add type annotations to the variables,
we run into an issue. Indeed, the variables are declared with the PlusCal
syntax:

```tla
{{#include ../../../test/tla/bakery-pluscal/BakeryWoTlaps.tla:71:74}}
```

The most straightforward approach would be to add type annotations directly in
the PlusCal code. As reported in [Issue 1412][], this does not work as
expected, as the PlusCal translator erases the comments.

A simple solution is to add type annotations directly to the declarations in
the generated TLA+ code. However, this solution is fragile. If we change the
PlusCal code, our annotations will get overridden. We propose another solution
that is stable under modification of the PlusCal code. To this end, we
introduce a new module called `BakeryTyped.tla` with the following contents:

```tla
{{#include ../../../test/tla/bakery-pluscal/BakeryTyped.tla:1:26}}
```

Due to the semantics of `INSTANCE`, the constants and variables declared in
`BakeryTyped.tla` substitute the constants and variables of
`BakeryWoTlaps.tla`. By doing so we effectively introduce type annotations.
Since we introduce a separate module, any changes in the PlusCal code do not
affect our type annotations.

Additionally, we add a constant initializer `ConstInit4`, which we will use
later. See the manual section about the [ConstInit predicate][] for a detailed
explanation.

## Step 2: Annotate the operator `\prec`

Let us run the type checker against `BakeryTyped.tla`:

```sh
$ apalache-mc typecheck BakeryTyped.tla
...
[BakeryWoTlaps.tla:66:17-66:20]: Cannot apply a to the argument 1 in a[1].
...
```

The type checker complains about types of `a` and `b` in the operator `\prec`:

```tla
{{#include ../../../test/tla/bakery-pluscal/BakeryWoTlaps.tla:66:67}}
```

The issue is that the type checker is not able to decide whether `a` and `b`
are functions, sequences, or tuples. We help the type checker by adding type
annotations to the operator `\preceq`.

```tla
{{#include ../../../test/tla/bakery-pluscal/BakeryWoTlaps.tla:63:67}}
```

When we run the type checker once again, it computes all types without
any problem:

```sh
$ apalache-mc typecheck BakeryTyped.tla
...
Type checker [OK]
```

Note that our annotation of `\preceq` would not get overwritten, when we update
the PlusCal code. This is because `\preceq` is defined in the TLA+ section.

## Step 3: Checking mutual exclusion for bounded executions

Once we have annotations, we run Apalache to check the property of mutual
exclusion for four processes and executions of length up to 10 steps:

```sh
$ apalache-mc apalache-mc check \
    --cinit=ConstInit4 --inv=MutualExclusion BakeryTyped.tla
...
It took me 0 days  0 hours 32 min  2 sec
```

Apalache reports no violation of `MutualExclusion`. This is a good start.
However, since Apalache only analyzes executions that make up to 10
transitions by default, this analysis is incomplete.

## Step 4: Checking mutual exclusion for unbounded executions

To analyze executions of arbitrary length with Apalache, we can check an
inductive invariant. For details, see the section on [Checking inductive
invariants][]. The Bakery specification contains such an invariant written by
Leslie Lamport:

```tla
{{#include ../../../test/tla/bakery-pluscal/BakeryWoTlaps.tla:258:275}}
```

To prove that `Inv` is an inductive invariant for `N = 4`, we run Apalache
twice. First, we check that the initial states satisfy the invariant `Inv`:

```sh
$ apalache-mc apalache-mc check --cinit=ConstInit4 \
    --init=Init --inv=Inv --length=0 BakeryTyped.tla
...
The outcome is: NoError
It took me 0 days  0 hours  0 min  6 sec
```

Second, we check that for every state that satisfies `Inv`, the following
holds true: Its successors via `Next` satisfy `Inv` too. This is done as
follows:

```sh
$ apalache-mc apalache-mc check --cinit=ConstInit4 \
    --init=Inv --inv=Inv --length=1 BakeryTyped.tla
...
The outcome is: NoError
It took me 0 days  0 hours  0 min 28 sec
```

Now we know that `Inv` is indeed an inductive invariant. Hence, we check
the property `MutualExclusion` against the states that satisfy `Inv`:

```sh
$ apalache-mc apalache-mc check --cinit=ConstInit4 \
    --init=Inv --inv=MutualExclusion --length=0 BakeryTyped.tla
...
The outcome is: NoError
It took me 0 days  0 hours  0 min 9 sec
```

In particular, these three results allow us to conclude that `MutualExclusion`
holds for all states that are reachable from the initial states (satisfying
`Init`) via the available transitions (satisfying `Next`). Since we have fixed
the constant `N` with the predicate `ConstInit4`, this result holds true for `N
= 4`. If you want to check `MutualExclusion` for other values of `N`, you can
define a predicate similar to `ConstInit4`. We cannot check the invariant for
all values of `N`, as this would require Apalache to reason about unbounded
sets and functions, which is currently not supported.

## Dealing with the define block

PlusCal specifications may contain the special define-block. For example:

```tla
---- MODULE CountersPluscal ----

(*
  Pluscal code inside TLA+ code.

--algorithm Counters {
  variable x = 0;

  define {
    \* This is TLA+ code inside the PlusCal code.
    IsPositive(x) == x > 0
  }

  ...
}
*)
================================
```

Unfortunately, the PlusCal transpiler erases comments when translating PlusCal
code to TLA+. Hence, the simplest solution is to move the define-block outside
the PlusCal code. For example:

```tla
---- MODULE CountersPluscal ----

\* @type: Int => Bool;
IsPositive(x) == x > 0

(*
--algorithm Counters {
  variable x = 0;

  ...
}
*)
================================
```

## Conclusion

The final specifications can be found in
[BakeryTyped.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bakery-pluscal/BakeryTyped.tla)
and
[BakeryWoTlaps.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bakery-pluscal/BakeryWoTlaps.tla).

In this tutorial we have shown how to:

 - Annotate a PlusCal spec with types by introducing an additional TLA+ module.
 - Check safety of Bakery for bounded executions by bounded model checking (for
   `N=4`).
 - Check safety of Bakery for unbounded executions by invariant checking (for
   `N=4`).

If you are experiencing a problem with Apalache, feel free to [open an issue]
or drop us a message on [Zulip chat].

## Further reading

 - [Entry-level Tutorial on the Model Checker][]
 - [Tutorial on Snowcat][] shows how to write type annotations for Apalache.
 - [TLA+ Cheatsheet in HTML][] summarizes the common TLA+ constructs. If you
   prefer a printable version in pdf, check the [Summary of TLA+][].


[PlusCal specification]: https://github.com/tlaplus/Examples/blob/master/specifications/Bakery-Boulangerie/Bakery.tla
[Bakery.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/Bakery-Boulangerie/Bakery.tla
[BakeryWoTlaps.tla]: https://github.com/informalsystems/apalache/blob/main/test/tla/bakery-pluscal/BakeryWoTlaps.tla
[Entry-level Tutorial on the Model Checker]: ./entry-tutorial.md
[HOWTO on writing type annotations]: ../HOWTOs/howto-write-type-annotations.md
[Apalache installation]: ../apalache/installation/index.md
[Leslie Lamport]: https://lamport.azurewebsites.net/
[Issue 1412]: https://github.com/informalsystems/apalache/issues/1412
[open an issue]: https://github.com/informalsystems/apalache/issues
[Tutorial on Snowcat]: ./snowcat-tutorial.md
[Checking inductive invariants]: https://apalache.informal.systems/docs/apalache/running.html#checking-an-inductive-invariant
[TLA+ Cheatsheet in HTML]: https://mbt.informal.systems/docs/tla_basics_tutorials/tla+cheatsheet.html
[Summary of TLA+]: https://lamport.azurewebsites.net/tla/summary-standalone.pdf
[TLA+ Video Course]: http://lamport.azurewebsites.net/video/videos.html
[ConstInit predicate]: ../apalache/parameters.html#constinit-predicate
[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=learning.html
[TLC]: https://github.com/tlaplus/tlaplus/
[TLAPS]: https://tla.msr-inria.inria.fr/tlaps/content/Home.html
[Zulip chat]: https://informal-systems.zulipchat.com/login/#narrow/stream/265309-apalache
[Bakery algorithm]: https://en.wikipedia.org/wiki/Lamport%27s_bakery_algorithm
[ZIP archive]: https://download-directory.github.io/?url=https://github.com/informalsystems/apalache/tree/main/test/tla/bakery-pluscal
