# How to write type annotations

**Revision:** August 24, 2022

**Important updates:**

 - Version 0.29.0: The new syntax for records and variants is enabled by
   default (previously, enabled with `--features=rows`). For the transition
   period, the old type syntax can be activated with `--features=no-rows`.
   See [Recipe 9](#recipe9) on transitioning to Type System 1.2.

 - Version 0.25.10: This HOWTO introduces new syntax for type aliases. See
   [Type Aliases][] in ADR-002.

 - Version 0.25.9: This HOWTO introduces new syntax for record types and
   variants, which is currently under testing. This syntax is activated via the
   option `--features=rows`. See [Type System 1.2](../adr/002adr-types.md#ts12)
   in ADR-002.

 - Version 0.23.1: The example specification uses recursive operators, which
   were removed in version 0.23.1.

 - Version 0.15.0: This HOWTO discusses how to write type annotations for the type checker
   [Snowcat][], which is used in Apalache since version 0.15.0 (introduced in
   2021).

This HOWTO gives you concrete steps to extend TLA+ specifications with type
annotations. You can find the detailed syntax of type annotations in
[ADR002][]. The first rule of writing type annotations:

*Do not write any annotations at all, until the type checker [Snowcat][] is
asking you to write a type annotation.*

Of course, there must be an exception to this rule. You have to write type
annotations for CONSTANTS and VARIABLES. This is because Snowcat infers types
of declarations in isolation instead of analyzing the whole specification.
The good news is that the type checker finds the types of many operators
automatically. 

## Recipe 1: Annotating variables

Consider the example [HourClock.tla][] from [Specifying Systems][]:

```tla
{{#include ../../../test/tla/HourClock.tla}}
```

Without thinking much about the types, run the type checker:

```sh
$ apalache-mc typecheck HourClock.tla
```

The type checker complains about not knowing the type of the variable `hr`:

```
...
Typing input error: Expected a type annotation for VARIABLE hr
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
...
 > Running Snowcat .::.
 > Your types are purrfect!
 > All expressions are typed
...
```

<a id="recipe2"></a>
## Recipe 2: Annotating constants

Consider the example [Channel.tla][] from [Specifying Systems][]:

```tla

{{#include ../../../test/tla/Channel.tla}}

```

Run the type checker:

```sh
$ apalache-mc typecheck Channel.tla
```

The type checker does not know the type of the variable `chan`:

```
Typing input error: Expected a type annotation for VARIABLE chan
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
{{#include ../../../test/tla/ChannelTyped.tla:declarations}}
```

Note carefully that the type annotation should be *between* the keyword
`CONSTANT` and the constant name. This is because constant declarations may
declare several constants at once. In this case, you have to write one type
annotation per name.

Have a look at the type of `chan`:

```
\* @type: { val: DATUM, rdy: Int, ack: Int };
```

The type of `chan` is a record that has three fields: field `val` of type
`DATUM`, field `rdy` of type `Int`, field `ack` of type `Int`. The record type syntax is similar to dictionary syntax from programming languages (e.g. Python). We made it different
from TLA+'s syntax for records `[ val |-> v, rdy |-> r, ack |-> a ]`
and record sets `[ val: V, rdy: R, ack: A ]`, to avoid confusion between
types and values.

Run the type checker again. You should see the following message:

```
$ apalache-mc typecheck ChannelTyped.tla
...
> Running Snowcat .::.
> Your types are purrfect!
> All expressions are typed 
```

## Recipe 3: Annotating operators

Check the example [CarTalkPuzzle.tla][] from the repository of TLA+
examples. This example has 160 lines of code, so we do not inline it here.
By running the type checker as in previous sections, you should figure out
that the constants `N` and `P` should be annotated with the type `Int`.
Annotate `N` and `P` with `Int` and run the type checker:

```sh
$ apalache-mc typecheck CarTalkPuzzle.tla
```

Now you should see the following error:

```
[CarTalkPuzzle.tla:52:32-52:35]: Cannot apply f to the argument x() in f[x()].
[CarTalkPuzzle.tla:50:1-52:53]: Error when computing the type of Sum
```

Although the error message may look confusing, the reason is simple: The type
checker cannot figure out whether the operator `Sum` expects a sequence
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
[CarTalkPuzzle.tla:160:23-160:26]: Cannot apply B to the argument x in B[x].
[CarTalkPuzzle.tla:160:7-160:37]: Error when computing the type of Image
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
...
> Running Snowcat .::.
> Your types are purrfect!
> All expressions are typed 
...
```

<a id="recipe4"></a>
## Recipe 4: Using variants in heterogenous sets

Check the example [TwoPhase.tla][] from the repository of TLA+ examples (you
will also need [TCommit.tla][], which is imported by TwoPhase.tla). This
example has 176 lines of code, so we do not inline it here.

As you probably expected, the type checker complains about not knowing
the types of constants and variables. As for constant `RM`, we opt for using
an uninterpreted type that we call `RM`. That is:

```tla
{{#include ../../../test/tla/TwoPhaseTyped.tla:constants}}
```

By looking at the spec, it is easy to guess the types of the variables
`rmState`, `tmState`, and `tmPrepared`:

```tla
{{#include ../../../test/tla/TwoPhaseTyped.tla:vars1}}
```

The type of the variable `msgs` is less obvious. We can check the original
(untyped) definitions of `TPTypeOK` and `Message` to get an idea about the
type of `msgs`:

```tla
Message ==
  ({[type |-> t, rm |-> r]: t \in {"Prepared"}, r \in RM }
   \union
   {[type |-> t] : t \in {"Commit", "Abort"}})

TPTypeOK ==
  ...
  /\ msgs \in SUBSET Message
```

From these (untyped) definitions, you can see that `msgs` is a set that
contains records of two types: `{ type: Str }` and `{ type: Str, rm: RM }`.
This seems to be problematic, as we have to mix in two records types in a
single set, which requires us to specify its only type.

To this end, we have to use the [Variants module][], which is distributed with
Apalache. For reference, check the [Chapter on variants][]. First, we declare a
type alias for the type of messages in a separate file called
`TwoPhaseTyped_typedefs.tla`:

```tla
{{#include ../../../test/tla/TwoPhaseTyped_typedefs.tla}}
```

Usually, we place type aliases in a separate file for when we have
to use the same type alias in different specifications, e.g., the specification
and its instance for model checking.

With the type alias `MESSAGE`, we specify that a message is a variant type,
that is, it can represent three kinds of different values:

 - A value tagged with `Commit`. Since we do not require the variant to carry
   any value here, we simply declare that the value has the uninterpreted type
   `NIL`. This is simply a convention, we could use any type in this case.

 - A value tagged with `Abort`. Similar to `Commit`, we are using the `NIL`
   type.

 - A value tagged with `Prepared`. In this case, the value is of importance.
   We are using the value `RM`, that is, the (uninterpreted) type of a resource
   manager.

Once we have specified the variant type, we introduce three constructors,
one per variant option:

```tla
{{#include ../../../test/tla/TwoPhaseTyped.tla:constructors}}
```

Since the values carried by the `Commit` and `Abort` messages are not
important, we use the uninterpeted value `"0_OF_NIL"`. This is merely a
convention. We could use any value of type `NIL`. Importantly, the operators
`MkAbort`, `MkCommit`, and `MkPrepared` all produce values of type `MESSAGE`,
which makes it possible to add them to a single set of messages.

Now it should be clear how to specify the type of the variable `msgs`:

```tla
{{#include ../../../test/tla/TwoPhaseTyped.tla:vars2}}
```

We run the type checker once again:

```sh
$ apalache-mc typecheck TwoPhaseTyped.tla
...
 > All expressions are typed
Type checker [OK]
```

As you can see, variants require quite a bit of boilerplate. If you can simply
introduce a set of records of the same type, this is usually a simpler
solution. For instance, we could partition `msgs` into three subsets: the
subset of `Commit` messages, the subset of `Abort` messages, and the subset of
`Prepared` messages. See the discussion in [Idiom 15][].

<a id="funAsSeq"></a>
## Recipe 5: functions as sequences

Check the example [Queens.tla][] from the repository of TLA+ examples.  It has
85 lines of code, so we do not include it here. Similar to the previous
sections, we annotate constants and variables:

```tla
{{#include ../../../test/tla/QueensTyped.tla:constants}}
...
{{#include ../../../test/tla/QueensTyped.tla:variables}}
```

After having inspected the type errors reported by Snowcat, we annotate the
operators `Attacks`, `IsSolution`, and `vars` as follows:

```tla
{{#include ../../../test/tla/QueensTyped.tla:Attacks}}
  ...

{{#include ../../../test/tla/QueensTyped.tla:IsSolution}}
  ...

{{#include ../../../test/tla/QueensTyped.tla:vars}}
```

Now we run the type checker and receive the following type error:

```
[Queens.tla:35:44-35:61]: The operator IsSolution of type ((Seq(Int)) => Bool) is applied to arguments of incompatible types in IsSolution(queens):
Argument queens should have type Seq(Int) but has type (Int -> Int). E@11:07:53.285
[Queens.tla:35:1-35:63]: Error when computing the type of Solutions
```

Let's have a closer look at the problematic operator definition of `Solutions`:

```tla
Solutions ==
    { queens \in [1..N -> 1..N]: IsSolution(queens) }
```

This looks interesting: `IsSolution` expects a sequence, whereas
`Solutions` produces a set of functions. This is obviously not a
problem in untyped TLA+. In fact, it is a well-known idiom: Construct a
function by using the function set operator, and then apply sequence operators to it.
In Apalache we have to explicitly write that a function should be reinterpreted
as a sequence.  To this end, we have to use the operator `FunAsSeq` from the
module [Apalache.tla][]. Hence, we add `Apalache` to the `EXTENDS` clause and
apply the operator `FunAsSeq` as follows:

```tla
EXTENDS Naturals, Sequences, Apalache
...
Solutions ==
  LET Queens == { FunAsSeq(queens, N, N): queens \in  [1..N -> 1..N] } IN
  {queens \in Queens : IsSolution(queens)}
```    


This time the type checker can find the types of all expressions:

```
> Running Snowcat .::.
> Your types are purrfect!
> All expressions are typed
```

<a id="typeAliases"></a>
## Recipe 6: type aliases

Type aliases can be used to provide a concise label for complex types, or to
clarify the intended meaning of a simple types in the given context. 

Type aliases are declared with the `@typeAlias` annotation, as follows:

```tla
\* @typeAlias: aliasNameInCamelCase = <type>;
```

For example, suppose we have annotated some constants as follows:

```tla
CONSTANTS
    \* @type: Set(PERSON);
    Missionaries,
    \* @type: Set(PERSON);
    Cannibals 
```

If we continue annotating other declarations in the specification, we will see
that the type `Set(PERSON)` is used frequently. Type aliases let us provide a 
shortcut.

By convention, we introduce all type aliases by annotating an operator called
`<PREFIX>_typedefs`, where the `<PREFIX>` is replaced with a unique prefix to
prevent name clashes across different modules. Typically `<PREFIX>` is just the
module name. For the [MissionariesAndCannibalsTyped.tla][] example, we have:

```tla
\* @typeAlias: persons = Set(PERSON);
MissionariesAndCannibals_typedefs = TRUE
```

Having defined the type alias, we can use it in other definitions anywhere else 
in the file:

```tla
CONSTANTS
    \* @type: $persons;
    Missionaries,
    \* @type: $persons;
    Cannibals 

VARIABLES
    \* @type: Str;
    bank_of_boat,
    \* @type: Str -> $persons;
    who_is_on_bank 
```

Surely, we did not gain much by writing `$persons` instead of `Set(PERSON)`.
But if your specification has complex types (e.g., records), aliases may help
you in minimizing the burden of specification maintenance. If you add one
more field to the record type, it suffices to change the definition of the type
alias, instead of changing the record type everywhere.

For more details on the design and usage, see [Type Aliases][] in ADR-002.

## Recipe 7: Multi-line annotations

A type annotation may span over multiple lines. You may use both the `(* ...
*)` syntax as well as the single-line syntax `\* ...`. All three examples below
are accepted by the parser:

```tla
VARIABLES
   (*
    @type: Int
            => Bool;
    *)           
    f,
    \* @type:
    \*       Int
    \*          => Bool;
    g,
    \* @type("Int
    \*          => Bool
    \*       ")
    h
```

Note that the parser removes the leading strings `"    \*"` from the annotations,
similar to how multi-line strings are treated in modern programming languages.

## Recipe 8: Comments in annotations

Sometimes, it helps to document the meaning of type components. Consider the following
example from [Recipe 5](#funAsSeq):

```tla
\* @type: (Seq(Int), Int, Int) => Bool;
Attacks(queens,i,j)
```

If you think that an explanation of the arguments would help, you can do that as follows:

```tla
(*
  @type:
    (
      // the column of an n-th queen, for n in the sequence domain
      Seq(Int),
      // the index (line number) of the first queen
      Int,
      // the index (line number) of the second queen
      Int
    ) => Bool;
*)
Attacks(queens,i,j)
```

You don't have to do that, but if you feel that types can also help you in documenting
your specification, you have this option.

<a id="recipe9"></a>
## Recipe 9: Migrate from Type System 1 to Type System 1.2

As explained in [ADR002][], [Type System 1.2][] (TS1.2) differs from [Type
System 1][] (TS1) as follows:

 - TS1 allows one to mix records of varying domains, as long as the records
   agree on the types of the common fields. Hence, record access is not
   enforced by the type checker and thus is error-prone.

 - TS1 is using the syntax `[ field_n: T_1, ..., field_n: T_n ]`, which is
   sometimes confused with the TLA+ expression `[ field_n: e_1, ..., field_n:
   e_n ]`.

 - TS1.2 is using the syntax `{ field_n: T_1, ..., field_n: T_n }`
   for record types and the syntax `Tag_1(T_1) | ... | Tag_n(T_n)`
   for variant types.

 - TS1.2 differentiates between records of different domains and does not allow
   the specification writer to mix them. As a result, TS1.2 can catch incorrect
   record access. Instead of mixing records, TS1.2 allows one to mix
   [Variants][].

 - TS1.2 supports [Row polymorphism][] and thus lets the user write type
   annotations over records and variants, whose shape is only
   partially-defined.  For example, `{ foo: Int, bar: Bool, a }` defines a
   record type that has at least two fields (that is, `foo` of type `Int` and
   `bar` of type `Bool`), but may have more fields, which are captured with the
   row variable `a`.

### Case 1: plain records

Many specifications are using plain records. For instance, they do not assign
records of different domains to the same variable. Nor do they mix records of
different domains in the same set. Plenty of specifications fall into this
class.

For example, check [Recipe 2](#recipe2). In this recipe, the variable `chan` is
always carrying a record with the domain `{ "val", "rdy", "ack" }`.

In this case, all you have to do is to replace the old record types of the form
`[ field_n: T_1, ..., field_n: T_n ]` with the new record types of the form `{
field_n: T_1, ..., field_n: T_n }`. That is, replace `[` and `]` with `{` and
`}`, respectively.

### Case 2: mixed records

Some specifications are using mixed records, which are similar to unions in C.

For example, check [Recipe 4](#recipe4). In this recipe, the variable
`tmPrepared` is a set that contains records of different domains. For instance,
`tmPrepared` may be equal to:

```tla
{ [ type |-> "Commit" ], [ type |-> "Prepared", rm |-> "0_OF_RM" ] }
```

In this case, you have two choices:

 - Partition the single variable into multiple variables, see [Idiom 15][].

 - Introduce variant types, see [Recipe 4](#recipe4).


## Known issues

### Annotations of LOCAL operators

In contrast to all other cases, a local operator definition does require
a type annotation before the keyword `LOCAL`, not after it. For example:

```tla
\* @type: Int => Int;
LOCAL LocalInc(x) == x + 1
```

This may change later, when the tlaplus [Issue 578][] is resolved.


[old type annotations]: ../apalache/types-and-annotations.md
[Apalache.tla]: https://github.com/informalsystems/apalache/blob/main/src/tla/Apalache.tla
[Snowcat]: ../apalache/typechecker-snowcat.md
[ADR002]: ../adr/002adr-types.md
[Type System 1]: ../adr/002adr-types.md#ts1
[Type System 1.2]: ../adr/002adr-types.md#ts12
[HourClock.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/RealTime/HourClock.tla
[Channel.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/FIFO/Channel.tla
[CarTalkPuzzle.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/CarTalkPuzzle/CarTalkPuzzle.tla
[TwoPhase.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla
[TCommit.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TCommit.tla
[Queens.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/N-Queens/Queens.tla
[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=learning.html#book
[Issue 401]: https://github.com/informalsystems/apalache/issues/401
[Issue 578]: https://github.com/tlaplus/tlaplus/issues/578
[Issue 718]: https://github.com/informalsystems/apalache/issues/718
[MissionariesAndCannibals.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/MissionariesAndCannibals/MissionariesAndCannibals.tla
[Variants module]: https://github.com/informalsystems/apalache/blob/main/src/tla/Variants.tla
[Chapter on variants]: ../lang/variants.md
[Variants]: ../lang/variants.md
[Idiom 15]: ../idiomatic/003record-sets.md
[LamportMutex.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/lamport_mutex/LamportMutex.tla
[Type Aliases]: ../adr/002adr-types.md#defTypeAlias
[MissionariesAndCannibalsTyped.tla]: https://github.com/informalsystems/apalache/blob/main/test/tla/MissionariesAndCannibalsTyped.tla
[Row polymorphism]: https://en.wikipedia.org/wiki/Row_polymorphism
