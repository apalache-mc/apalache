# Tutorial on the Snowcat:snowflake::cat: Type Checker

**Difficulty: Blue trail – Easy**

**Revision:** August 24, 2022

In this tutorial, we introduce the Snowcat :snowflake: :cat: type checker.
We give concrete steps to running the type checker and annotating a specification
with types.

This tutorial uses Type System 1.2, which guarantees safe record access. To see
how to upgrade to Type System 1.2, check [Migrating to Type System 1.2][].

## Related documents

- [ADR002][] that introduces Type Systems 1 and 1.2, used by Snowcat.
- A more technical [HOWTO on writing type annotations][].
- [ADR004][] that introduces Java-like annotations in TLA+ comments.

## Setup

We assume that you have Apalache installed. If not, check the manual page on
[Apalache installation][]. The minimal required version is 0.29.0.

## Running example: Lamport's mutex

As a running example, we are using the specification of [Lamport's Mutex][]
(written by [Stephan Merz][]). We recommend to reproduce the steps in this
tutorial. So, go ahead and download the specification file
[LamportMutex.tla][]. We will add type annotations to this file. Let's rename
`LamportMutex.tla` to `LamportMutexTyped.tla`.

## Step 1: Running Snowcat

Before we start writing any type annotations, let's run the type checker and
see, whether it complains:

```sh
$ apalache-mc typecheck LamportMutexTyped.tla
```

The tool output is a bit verbose. Below, you can see the important lines of the
output:

```
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.                                           
Typing input error: Expected a type annotation for VARIABLE clock
... 
```

## Step 2: Annotating variables clock, req, ack, crit

In Step 1, Snowcat complained about the name `clock`. The reason
for that is very simple: `clock` is declared as a variable, but Snowcat 
does not find a type annotation for it.

The comment next to the declaration of `clock` does not tell us precisely
what `clock` should be:

```
  clock,    \* local clock of each process
```

Let's dig a bit further and check `TypeOK`, which is usually a good source of
type hints in untyped specifications:

```tla
{{#include ../../../test/tla/LamportMutexTyped.tla:TypeOK}}
```

This is better, but we have to figure out the types of `Proc` and `Clock`.
Let's have a look at their definitions.

```tla
{{#include ../../../test/tla/LamportMutexTyped.tla:ProcAndClock}}
```

From the definitions of `Proc` and `Clock`, it is clear that they are both
subsets of integers. We could annotate these two definitions with the type
`Set(Int)`, but this is not necessary, since Snowcat will infer these types
itself.

Together with `TypeOK`, this gives us enough information to annotate all but
one variable (we will annotate the variable `network` later):

```tla
{{#include ../../../test/tla/LamportMutexTyped.tla:vars1}}
```

In our type annotations:

 - `clock` belongs to the set `[Proc -> Clock]`. Hence, it is a function of
   integers to integers, that is, `Int -> Int`.

 - `req` belongs to the set `[Proc -> [Proc -> Nat]]`. Hence, it is a function
   of integers to functions of integers to integers, that is, `Int -> (Int ->
   Int)`.

 - `ack` belongs to the set `[Proc -> SUBSET Proc]`. Hence, it is a function of
   integers to sets of integers, that is, `Int -> Set(Int)`.

 - `crit` is a subset of `Proc`, so it is a set of integers, that is,
   `Set(Int)`.

**Note**: We place the annotation for `clock` between the keyword `VARIABLES`
and `clock`, not before the keyword `VARIABLES`. Similarly, we added a type
annotation immediately above every other variable name.

We used the one-line TLA+ comment for `clock`:

```tla
\* @type: Int -> Int;
```

Alternatively, we could use the multi-line comment:

```tla
(*
 Clock is a function of integers to integers.

 @type: Int -> Int;
 *)
```

**Note**: Importantly, every type annotation must end with a semicolon `;`.

Let's run the type checker again:

```sh
$ apalache-mc typecheck LamportMutexTyped.tla
...
Typing input error: Expected a type annotation for VARIABLE network
```

Not surprisingly, the type checker tells us that we still have to annotate the
variable `network`.

## Step 3: Annotating the variable network

Let's have a look at the operator `TypeOK` again:

```tla
{{#include ../../../test/tla/LamportMutexTyped.tla:TypeOK}}
```

From this we can see that `network` is a function of integers to a function of
integers to a sequence of messages. So its type should look like:

```tla
Int -> (Int -> Seq(/* message type */))
```

But what is the message type? To find out, we have to continue our archaeology
trip and check the definition of `Message` and related operators:

```tla
{{#include ../../../test/tla/LamportMutexTyped.tla:Message}}
```

From these four definitions, we can see that `Messages` is a set of records
that have two fields: the field `type` that should be a string, and the field
`clock` that should be an integer. In Apalache, we write such a record type as:

```tla
{ type: Str, clock: Int }
```

Hence, the type of `network` should be:

```tla
Int -> (Int -> Seq({ type: Str, clock: Int }))
```

We could write it as above, but that type is a bit hard to read. Hence, we
split it into two parts: the type alias `message` that defines the type of
messages, and the type of `network` that refers to the type alias `message`.
This can be done in the following way:

```tla
{{#include ../../../test/tla/LamportMutexTyped.tla:vars2}}
```

**Note:** We are lucky that `ReqMessage`, `AckMessage`, and `RelMessage` are
producing records of the same shape. In some specifications, the shapes of
records differ, while these records should be added to the same set. This is a
bit problematic for the type checker, as it expects set elements to have the
same type. In this case, we have three options:

 - Slightly rewrite the specification to homogenize records,

 - Partition the set of messages into several sets, see [Idiom 15][], or

 - Use variants. This is a more advanced topic, see the
   [HOWTO on writing type annotations][].

Now we should run the type checker again:

```sh
$ apalache-mc typecheck LamportMutexTyped.tla
...
Typing input error: Expected a type annotation for CONSTANT maxClock
```

The type checker is still not happy: We have not annotated `CONSTANTS`.

## Step 4: Annotating constants

Now we have to figure out the types of the constants: `N` and `maxClock`.  This
is fairly easy, as these constants are accompanied by the two assumptions:

```tla
{{#include ../../../test/tla/LamportMutexTyped.tla:assumes}}
```

From these assumptions, we can conclude that both `N` and `maxClock` are
integers. We add the type annotations:

```tla
{{#include ../../../test/tla/LamportMutexTyped.tla:constants}}
```

Let's run the type checker once again:

```sh
$ apalache-mc typecheck LamportMutexTyped.tla
...
 > All expressions are typed
Type checker [OK]
```

Snowcat is happy, and so we are too!

# Discussion

To see the complete code, check [LamportMutexTyped.tla][]. We have added seven
type annotations for 184 lines of code. Not bad.

It was relatively easy to figure out the types of constants and variables in
our example, though it required some exploration of the specification.

*As a rule, you always have to annotate constants and variables with types*.

Hence, we did not have to run the type checker seven times to see the error
messages.  The type annotations are useful on its own, since we do not have to
traverse the spec to figure out the types of constants and states. Our more
engineering-oriented peers find these annotations to be quite important.

Sometimes, the type checker cannot find a unique type of an expression. This
usually happens when you declare an operator of a parameter that can be: a
function, a tuple, a record, or a sequence (or a subset of these four types
that has at least two elements). For instance, here is a definition from
[GameOfLifeTyped.tla][]:

```tla
Pos ==
    { <<x, y>>: x, y \in 1..N }
```

Although it is absolutely clear that `x` and `y` have the type `Int`,
the type of `<<x, y>>` is ambiguous. This expression can either be
a tuple `<<Int, Int>>`, or a sequence `Seq(Int)`. In this case, we have to
help the type checker by annotating the operator definition:

```tla
\* @type: () => Set(<<Int, Int>>);
Pos ==
    {<<x, y>>: x, y \in 1..N}
```

Since it is common to have operators that take no arguments, Snowcat supports
the following syntax sugar for operators without arguments:

```tla
\* @type: Set(<<Int, Int>>);
Pos ==
    {<<x, y>>: x, y \in 1..N}
```

## Further reading

For more advanced type annotations, check the following examples:

- [CigaretteSmokersTyped.tla][],
- [CarTalkPuzzleTyped.tla][],
- [QueensTyped.tla][].
- [TwoPhaseTyped.tla][].

We have not discussed type aliases, which are a more advanced feature of the
type checker. To learn about type aliases, see [HOWTO on writing type
annotations][].

If you are experiencing a problem with Snowcat, feel free to [open an issue][]
or drop us a message on [Zulip chat][].


[ADR002]: ../adr/002adr-types.md
[ADR004]: ../adr/004adr-annotations.md
[HOWTO on writing type annotations]: ../HOWTOs/howto-write-type-annotations.md
[Migrating to Type System 1.2]: ../HOWTOs/howto-write-type-annotations.md#recipe9
[Apalache installation]: ../apalache/installation/index.md
[Two-phase commit]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit
[Lamport's mutex]: https://github.com/tlaplus/Examples/blob/master/specifications/lamport_mutex
[TwoPhase.tla]: https://github.com/tlaplus/Examples/blob/911dac1462344337940779a797a5f329a77be98c/specifications/transaction_commit/TwoPhase.tla
[LamportMutex.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/lamport_mutex/LamportMutex.tla
[LamportMutexTyped.tla]: https://github.com/informalsystems/apalache/blob/main/test/tla/LamportMutexTyped.tla
[TwoPhaseTyped.tla]: https://github.com/informalsystems/apalache/blob/main/test/tla/TwoPhaseTyped.tla
[Stephan Merz]: https://members.loria.fr/Stephan.Merz/
[GameOfLifeTyped.tla]: https://github.com/informalsystems/apalache/blob/main/test/tla/GameOfLifeTyped.tla
[CigaretteSmokersTyped.tla]: https://github.com/informalsystems/apalache/blob/main/test/tla/CigaretteSmokersTyped.tla
[CarTalkPuzzleTyped.tla]: https://github.com/informalsystems/apalache/blob/main/test/tla/CarTalkPuzzleTyped.tla
[QueensTyped.tla]: https://github.com/informalsystems/apalache/blob/main/test/tla/QueensTyped.tla
[open an issue]: https://github.com/informalsystems/apalache/issues
[Zulip chat]: https://informal-systems.zulipchat.com/login/#narrow/stream/265309-apalache
[Idiom 15]: ../idiomatic/003record-sets.md
