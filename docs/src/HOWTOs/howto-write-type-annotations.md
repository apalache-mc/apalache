# How to write type annotations

**Warning:** *This HOWTO discusses how to write type annotations for the new
type checker [Snowcat][], which is used in Apalache since version 0.15.0.*

This HOWTO gives you concrete steps to extend TLA+ specifications with type
annotations. You can find the detailed syntax of type annotations in
[ADR002][]. The first rule of writing type annotations:

*Do not to write any annotations at all, until the type checker [Snowcat][] is
asking you to write a type annotation.*

Of course, there must be an exception to this rule. You have to write type
annotations for CONSTANTS and VARIABLES. This is because Snowcat infers types
of declarations in isolation instead of analyzing the whole specification.
The good news is that the type checker finds the types of many operators
automatically. 

## Recipe 1: Recipe variables

Consider the example [HourClock.tla][] from [Specifying Systems][]:

```tla
{{#include ../../../test/tla/HourClock.tla::13}}
```

Without thinking much about the types, run the type checker:

```sh
$ apalache typecheck HourClock.tla
```

The type checker complains about not knowing the type of the variable `hr`:

```
...
[HourClock.tla:6:12-6:13]: Undefined name hr. Introduce a type annotation.
...
```

Annotate the type of variable `hr` as below. Note carefully that the type
annotation should be *between* the keyword `VARIABLE` and the variable name.
This is because variable declarations may declare several variables at once.
In this case, you have to write one type annotation per name.

```tla
VARIABLE
  \* @type: Int;
  hr
```

Run the type checker again. You should see the following message:

```
 > Your types are great!
```

## Recipe 2: Annotating constants

Consider the example [Channel.tla][] from [Specifying Systems][]:

```tla

{{#include ../../../test/tla/Channel.tla::28}}

```

Run the type checker:

```sh
$ apalache typecheck Channel.tla
```

The type checker does not know the type of the variable `chan`:

```
[Channel.tla:6:20-6:23]: Undefined name chan. Introduce a type annotation.
```

According to `TypeInvariant`, the variable `chan` is a record that has three
fields: `val`, `rdy`, and `ack`. The field `val` ranges over a set `Data`,
which is actually defined as `CONSTANT`. In principle, we can annotate the
constant `Data` with a set of any type, e.g., `Set(Int)` or `Set(BOOLEAN)`.
Since the specification is not using any operators over `Data` except equality,
we can use an *uninterpreted type* as a type for set elements, e.g.,
we can define `Data` to have the type `Set(DATUM)`. Uninterpreted types are
always written in CAPITALS. Now we can annotate `Data` and `chan` as follows:

```tla
CONSTANT
    \* @type: Set(DATUM);
    Data
VARIABLE
    \* @type: [val: DATUM, rdy: Int, ack: Int];
    chan 
```

Note carefully that the type annotation should be *between* the keyword
`CONSTANT` and the constant name. This is because constant declarations may
declare several constants at once. In this case, you have to write one type
annotation per name.

Run the type checker again. You should see the following message:

```
 > Your types are great!
```

## Recipe 3: Annotating operators

Check the example [CarTalkPuzzle.tla][] from the repository of TLA+
examples. This example has 160 lines of code, so we do not inline it here.
By running the type checker as in previous sections, you should figure out
that the constants `N` and `P` should be annotated with the type `Int`.
Annotate `N` and `P` with `Int` and run the type checker:

```sh
$ apalache typecheck CarTalkPuzzle.tla
```

Now you should see the following error:

```
[CarTalkPuzzle.tla:57:9-57:12]: Need annotation. Arguments match
2 operator signatures: (((a56 -> a57), a56) => a57) and ((Seq(a56), Int) => a56)
```

Although the error message may look confusing, the reason is simple: The type
checker cannot figure out, whether the operator `Sum` expects a sequence
or a function of integers as its first parameter. By looking carefully at
the definition of `Sum`, we can see that it expects: (1) a function from
integers to integers as its first parameter, (2) a set of integers
as its second parameter, and (3) an integer as a result. Hence, we annotate
`Sum` as follows:

```tla
RECURSIVE Sum(_,_)
\* type: (Int -> Int, Set(Int)) => Int;
Sum(f,S) ==
    ...
```

Note that the annotation has to be written between `RECURSIVE Sum(_, _)` and
the definition of `Sum`. This might change later, see [Issue 578] at tlaplus.

After providing the type checker with the annotation for `Sum`, we get one
more type error:

```
[CarTalkPuzzle.tla:172:23-172:26]: Need annotation. Arguments match
2 operator signatures: (((p -> q), p) => q) and ((Seq(p), Int) => p)
```

This time the type checker cannot choose between two options for the second
parameter of `Image`: It could be a function, or a sequence. We help the
type checker by writing that the second parameter should be a function
of integers to integers, that is, `Int -> Int`:

```tla      
      \* @type: (Set(Int), Int -> Int) => Set(Int);
      Image(S, B) == {B[x] : x \in S}
```

This time the type checker can find the types of all expressions:

```
 > Your types are great!
```


## Recipe 4: Annotating records

Check the example [TwoPhase.tla][] from the repository of TLA+ examples. This
example has 176 lines of code, so we do not inline it here.

As you probably expected, the type checker complains about not knowing
the types of constants and variables. As for constant `RM`, we opt for using
an uninterpreted type that we call `RM`. That is:

```tla
CONSTANT
        \* @type: Set(RM);
        RM
```

By looking at the spec, it is easy to guess the types of the variables
`rmState`, `tmState`, and `tmPrepared`:

```tla
VARIABLES
  \* @type: RM -> Str;
  rmState,
  \* @type: Str;
  tmState,
  \* @type: Set(RM);
  tmPrepared
```

The type of the variable `msgs` is less obvious. We can check the definitions
of `TPTypeOK` and `Message` to get the idea about the type of `msgs`:

```tla
Message ==
  ({[type |-> t, rm |-> r]: t \in {"Prepared"}, r \in RM }
   \cup
   {[type |-> t] : t \in {"Commit", "Abort"}})

TPTypeOK ==
  ...
  /\ msgs \in SUBSET Message
```

From these definitions, you can see that `msgs` is a set that contains records
of two types: `[type: Str]` and `[type: Str, rm: RM]`. When you have a set of
heterogeneous records, you have to choose the type of a super-record that
contains the fields of all records that could be put in the set. That is:

```tla
  \* @type: Set([type: Str, rm: RM]);
  msgs           
```

A downside of this approach is that [Snowcat][] will not help you in finding
an incorrect field access. We probably will introduce more precise types for
records later. See [Issue 401][].


## Recipe 5: functions as sequences

Check the example [Queens.tla][] from the repository of TLA+ examples.  It has
85 lines of code, so we do not include it here. Similar to the previous
sections, we annotate constants and variables:

```tla
CONSTANT 
         \* @type: Int;
         N
...         
VARIABLES
    \* @type: Set(Seq(Int));
    todo,
    \* @type: Set(Seq(Int));
    sols
```

After having inspected the type errors reported by Snowcat, we annotate the
operators `Attacks`, `IsSolution`, and `vars` as follows:

```tla
\* @type: (Seq(Int), Int, Int) => Bool;
Attacks(queens,i,j) == ...

\* @type: Seq(Int) => Bool;
IsSolution(queens) == ...

\* @type: <<Set(Seq(Int)), Set(Seq(Int))>>;
vars == <<todo,sols>>
```

Now we run the type checker and receive the following type error:

```
[Queens.tla:47:21-47:38]: Mismatch in argument types.
Expected: ((Seq(Int)) => Bool)
```

Let's have a closer look at the problematic operator definition of `Solutions`:

```tla
Solutions ==
    { queens \in [1..N -> 1..N]: IsSolution(queens) }
```

This looks funny: `IsSolution` is expecting a sequence, whereas `Solutions` is
clearly producing a set of functions. Of course, it is not a problem in the
untyped TLA+. In fact, it is a well-known idiom: Construct a function by using
function operators and then apply sequence operators to it. In Apalache we have
to explicitly write that a function should be reinterpreted as a sequence.  To
this end, we have to use the operator `FunAsSeq` from the module
[Apalache.tla][]. Hence, we add `Apalache` to the `EXTENDS` clause and
apply the operator `FunAsSeq` as follows:

```tla
EXTENDS Naturals, Sequences, Apalache
...
Solutions ==
  LET Queens == { queens \in [1..N -> 1..N] : FunAsSeq(queens, N) } IN
  { FunAsSeq(queens, N): queens \in Queens }
```    


This time the type checker can find the types of all expressions:

```
 > Your types are great!
```

## Known issues

In contrast to all other cases, a local operator definition does require
a type annotation before the keyword `LOCAL`, not after it. For example:

```tla
\* @type: Int => Int;
LOCAL LocalInc(x) == x + 1
```

This may change later, when the tlaplus [Issue 578][] is resolved.


[old type annotations]: ../apalache/types-and-annotations.md
[Apalache.tla]: https://github.com/informalsystems/apalache/blob/unstable/src/tla/Apalache.tla
[Snowcat]: ../apalache/typechecker-snowcat.md
[ADR002]: ../adr/002adr-types.md
[HourClock.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/RealTime/HourClock.tla
[Channel.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/FIFO/Channel.tla
[CarTalkPuzzle.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/CarTalkPuzzle/CarTalkPuzzle.tla
[TwoPhase.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla
[Queens.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/N-Queens/Queens.tla
[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=learning.html#book
[Issue 401]: https://github.com/informalsystems/apalache/issues/401
[Issue 578]: https://github.com/tlaplus/tlaplus/issues/578
