# Tutorial on the Snowcat:snowflake::cat: Type Checker

In this tutorial, we introduce the Snowcat :snowflake: :cat: type checker
We give concrete steps on running the type checker and
annotating a specification with types.

## Related documents

- [ADR002][] that introduces Type System 1, which is used by Snowcat.
- A more technical [HOWTO on writing type annotations][].
- [ADR004][] that introduces Java-like annotations in TLA+ comments.

## Setup

We assume that you have Apalache installed. If not, check the manual page on
[Apalache installation][]. The minimal required version is 0.15.0.

## Running example: Two-phase commit

As a running example, we are using the well-understood specification of
[Two-phase commit][] by [Leslie Lamport][] (written by [Stephan Merz][]). We
recommend to reproduce the steps in this tutorial. So, go ahead and download
two specification files: [TwoPhase.tla][] and [TCommit.tla][].

## Step 1: Running Snowcat

Before we start writing any type annotations, let's run the type checker and
see, whether it complains:

```sh
$ apalache typecheck TwoPhase.tla
```

The tool output is a bit verbose. Below, you can see the important lines of the
output:

```
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
[TwoPhase.tla:51:30-51:31]: Undefined name RM. Introduce a type annotation.
 > Snowcat asks you to fix the types. Meow.
... 
```

## Step 2: Annotating RM

In Step 1, Snowcat complained about the name `RM`. The reason
for that is very simple: Snowcat does type analysis for each declaration in
isolation. Hence, it failed, as soon as it met a reference to the constant
`RM` in the definition of `Message`:

```tla
CONSTANT RM \* The set of resource managers
...

Message ==
  ...
  [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
```

Indeed, we have not introduced a type annotation for the constant `RM`, so the
type checker cannot use any meaningful type in the context of the above
expression.

From the comment next to the declaration of `RM`, we see that `RM` is supposed
to be a set of resource managers. We have plenty of choices here of what a
resource manager could be. Let's keep it simple and say that a resource manager
is simply a name. Hence, we say that `RM` is a set of strings. Let's add a 
type annotation:

```tla
CONSTANT
    \* @type: Set(Str);
    RM \* The set of resource managers
```

Note that we had to put the annotation between the keyword `CONSTANT` and the
identifier `RM`. We used the one-line TLA+ comment: `\* @type: ...;`.
Alternatively, we could use the multi-line comment: `(* @type: Set(Str); *)`.
Importantly, the type annotation should end with a semi-colon: `;`.

## Step 3: Running Snowcat again

Having introduced the type annotation for `RM`, let's run the type checker again:

```sh
$ apalache typecheck TwoPhase.tla
```

Snowcat does not complain about `RM` anymore. Now we get another message:

```
[TwoPhase.tla:68:6-68:12]: Undefined name rmState. Introduce a type annotation.
```

## Step 4: Annotating rmState

Similar to Step 2, we are missing a type annotation. This time the type checker
complains about the variable `rmState`:

```tla
VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
```

We can get a hint about the type of `rmState` from the type invariant
`TPTypeOK`. It should be a function that, given a resource manager, produces
one of the following strings: `"working"`, `"prepared"`, `"committed"`,
`"aborted"`. So we need the function type: `Str -> Str`. Add the following
type annotation:

```tla
VARIABLES
  \* @type: Str -> Str;
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
```

## Step 5: Getting one more type error by Snowcat

Guess what? Run the type checker again:

```sh
$ apalache typecheck TwoPhase.tla
```

Snowcat does not complain about `rmState` anymore. But we are not done yet:

```
[TwoPhase.tla:70:6-70:12]: Undefined name tmState. Introduce a type annotation.
```

## Step 6: Annotating tmState

This time we need a type annotation for the variable `tmState`. By inspecting
`TPTypeOK`, we see that `tmState` is just a string. Add the following type
annotation:

```tla
VARIABLES
  (* ... *)
  \* @type: Str;  
  tmState,       \* The state of the transaction manager.
```

## Step 7: Running Snowcat to see another error

Run the type checker again:

```sh
$ apalache typecheck TwoPhase.tla
```

You must have guessed that the type checker complains about the variable
`tmPrepared`. Indeed, it just needs annotations for all CONSTANTS and
VARIABLES:

```
[TwoPhase.tla:72:6-72:15]: Undefined name tmPrepared. Introduce a type annotation.
```

## Step 8: Annotating tmPrepared

At this step, we have to annotate `tmPrepared`. Let's have a look at the comment
next to the declaration of `tmPrepared`:

```tla
VARIABLES
  ...
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
```

Hence, `tmPrepared` is a set of resource managers. This is what we write as a
type annotation:

```tla
VARIABLES
  (* ... *)
  \* @type: Set(Str);
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
```

## Step 9: Running Snowcat again

You know that we have to run the type checker again:

```sh
$ apalache typecheck TwoPhase.tla
```

It is no surprise that it complains about the variable `msgs` now:

```
[TwoPhase.tla:74:6-74:9]: Undefined name msgs. Introduce a type annotation.
```

## Step 10: Annotating msgs

In the previous steps, it was quite easy to annotate variables. We would just
look at how the variable is used, or read the comments, and add a type annotation.
Figuring out the type of `msgs` is a bit harder.

Let's look at the definitions of `Messages` and `TPTypeOK`:

```tla
Message ==
  ...
  [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]

TPTypeOK ==  
  ...  
  /\ msgs \subseteq Message
```

Now you should be able to see that `msgs` is a set that may contain three
kinds of records:

1. The record `[type |-> "Commit"]`,
1. The record `[type |-> "Abort"]`,
1. A record `[type |-> "Prepared", rm |-> r]`, for some `r \in RM`.

This looks like an issue for the type checker, as it always requires
the set elements to have the same type. However, the type checker
did not complain about the expressions in `Message` and `TPTypeOK`. Why?

Actually, the type checker allows records to be generalized to a type that
contains additional fields. In the above definition of `Messages`, the set of
records `[type: {"Prepared"}, rm: RM]` has the type `Set([type: Str, rm:
Str])`.  (Note that the record has the field called "type", which has nothing
to do with our types.) Likewise, the set of records `[type: {"Commit",
"Abort"}]` has the type `Set([type: Str])`. Both of these types can be unified
to the common type:

```
Set([type: Str, rm: Str])
``` 

The above type is actually what we need for the variable `msgs`. Let's annotate
the variable with this type:

```tla
VARIABLES
  (* ... *)
  \* @type: Set([type: Str, rm: Str]);
  msgs
```

## Step 11: Running Snowcat and seeing no errors

Let's see whether Snowcat is happy about our types now:

```sh
$ apalache typecheck TwoPhase.tla
```

The type checker is happy. It has computed the types of all expressions:

```
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
```

# Discussion

To see the complete code, check [TwoPhase.tla](./TwoPhase.tla). Note that we
have not touched the file `TCommit.tla` at all! The type checker has figured
out all the types in it by itself. We have added five type annotations for 248
lines of code. Not bad.

It was quite easy to figure out the types of constants and variables in our
example. As a rule, you always have to annotate constants and variables with
types. Hence, we did not have to run the type checker five times to see the
error messages.

Sometimes, the type checker cannot find a unique type of an expression. This
usually happens when you declare an operator of a parameter that can be: a
function, a tuple, a record, or a sequence (or a subset of these four types
that has at least two elements). For instance, here is a definition from
[GameOfLifeTyped.tla][]:

```tla
Pos ==
    {<<x, y>>: x, y \in 1..N}
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
the following syntax sugar:

```tla
\* @type: Set(<<Int, Int>>);
Pos ==
    {<<x, y>>: x, y \in 1..N}
```

## Further reading

For more advanced type annotations, check the following examples:

- [CigaretteSmokersTyped.tla][],
- [CarTalkPuzzleTyped.tla][],
- [FunctionsTyped.tla][],
- [QueensTyped.tla][].

We have not discussed type aliases, which are a more advanced feature of the
type checker. To learn about type aliases, see [HOWTO on writing type
annotations][].

If you are experiencing a problem with Snowcat, feel free to [open an issue]
or drop us a message on [Zulip chat].


[ADR002]: ../adr/002adr-types.html
[ADR004]: ../adr/004adr-annotations.html
[HOWTO on writing type annotations]: ../HOWTOs/howto-write-type-annotations.md
[Apalache installation]: ../apalache/installation/index.md
[Two-phase commit]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit
[TwoPhase.tla]: https://github.com/tlaplus/Examples/blob/911dac1462344337940779a797a5f329a77be98c/specifications/transaction_commit/TwoPhase.tla
[TCommit.tla]: https://github.com/tlaplus/Examples/blob/911dac1462344337940779a797a5f329a77be98c/specifications/transaction_commit/TCommit.tla
[Leslie Lamport]: https://lamport.azurewebsites.net/
[Stephan Merz]: https://members.loria.fr/Stephan.Merz/
[GameOfLifeTyped.tla]: https://github.com/informalsystems/apalache/blob/d5138a33fce3d77abc07a39bfb4f448942e6f641/test/tla/GameOfLifeTyped.tla 
[CigaretteSmokersTyped.tla]: https://github.com/informalsystems/apalache/blob/d5138a33fce3d77abc07a39bfb4f448942e6f641/test/tla/CigaretteSmokersTyped.tla
[CarTalkPuzzleTyped.tla]: https://github.com/informalsystems/apalache/blob/d5138a33fce3d77abc07a39bfb4f448942e6f641/test/tla/CarTalkPuzzleTyped.tla
[FunctionsTyped.tla]: https://github.com/informalsystems/apalache/blob/d5138a33fce3d77abc07a39bfb4f448942e6f641/test/tla/FunctionsTyped.tla
[QueensTyped.tla]: https://github.com/informalsystems/apalache/blob/d5138a33fce3d77abc07a39bfb4f448942e6f641/test/tla/QueensTyped.tla
[open an issue]: https://github.com/informalsystems/apalache/issues
[Zulip chat]: https://informal-systems.zulipchat.com/login/#narrow/stream/265309-apalache
