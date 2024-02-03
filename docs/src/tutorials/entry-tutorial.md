# Entry-level Tutorial on the Model Checker

**Difficulty: Blue trail – Easy**

In this tutorial, we show how to turn an implementation of binary search into a
TLA+ specification. This implementation is known to have an out-of-bounds
error, which once existed in Java, see [Nearly All Binary Searches and
Mergesorts are Broken][] by Joshua Bloch (2006). Our goal is to write a
specification after this implementation, not to write a specification of an
abstract binary search algorithm. You can find such a specification and a proof
in [Proving Safety Properties][] and [Binary search with a TLAPS proof][] by
[Leslie Lamport][] (2019).

This tutorial is written under the assumption that the reader does not have any
knowledge of TLA+ and Apalache. Since we are not diving into protocol and
algorithm specifications too quickly, this is a nice example to start with. We
demonstrate how to use Apalache to find errors that are caused by integer
overflow and the out-of-bounds error, which is caused by this overflow. We
also show that the same overflow error prevents the algorithm from terminating
in the number of steps that is expected from the binary search. Normally it is
expected that the binary search terminates in `log2(n)` steps, where `n` is the
length of the search interval.

Sometimes, we refer to the model checker TLC in this text. TLC is another
model checker for TLA+ and was introduced in the late 90s.  If you are new
to TLA+ and want to learn more about TLC, check the [TLC][] project and the
[TLA+ Video Course][] by Leslie Lamport. If you are an experienced TLC user,
you will find this tutorial helpful too, as it demonstrates the strong points
of Apalache.

## Related documents

 - [Tutorial on Snowcat][] shows how to write type annotations for Apalache.
 - [TLA+ Cheatsheet in HTML][] summarizes the common TLA+ constructs.  If you
   prefer a printable version in pdf, check the [Summary of TLA+][].

## Setup

We assume that you have Apalache installed. If not, check the manual page on
[Apalache installation][]. The minimal required version is 0.22.0.

We provide all source files referenced in this tutorial as a [ZIP archive][]
download. We still recommend that you follow along typing the TLA+ examples
yourself.

## Running example: Binary search

We are not going to explain the idea of binary search in this tutorial. If you
need more context on this, check the Wikipedia page on the [Binary search
algorithm][]. Let's jump straight into the Java code that is given in [Nearly All
Binary Searches and Mergesorts are Broken][]:

```java
1:     public static int binarySearch(int[] a, int key) {
2:         int low = 0;
3:         int high = a.length - 1;
4:
5:         while (low <= high) {
6:             int mid = (low + high) / 2;
7:             int midVal = a[mid];
8:
9:             if (midVal < key)
10:                 low = mid + 1
11:             else if (midVal > key)
12:                 high = mid - 1;
13:             else
14:                 return mid; // key found
15:         }
16:         return -(low + 1);  // key not found.
17:     }
```

As was found by Joshua Bloch, the addition in line 6 may throw
an out of bounds exception at line 7, due to an integer overflow. This is because `low`
and `high` are signed integers, with a maximum value of `2^31 - 1`. 
However, the sum of two values, each smaller than `2^31-1`, may be greater than `2^31 -1`. If this  is the case, `low + high` can wrap into a negative number.

This bug was
[discussed](https://groups.google.com/g/tlaplus/c/msLltIcexF4/m/qnABiKJmDgAJ)
in the TLA+ User Group in 2015. Let's see how TLA+ and Apalache can help us
here. A bit of warning: The final TLA+ specification will happen to be longer
than the 17 lines above. Don't get disappointed too fast. There are several
reasons for that:

 1. TLA+ is not tuned towards one particular class of algorithms, e.g.,
 sequential algorithms.

 2. Related to the previous point, TLA+ and Apalache are not tuned to C or Java
 programs. A software model checker such as [CBMC][], [Stainless][], or
 [Coral][] would probably accept a shorter program, and it would check it
 faster. However, if you have a sledgehammer like TLA+, you don't have to learn
 other languages.

 3. We explicitly state the expected properties of the algorithm to be checked
 by Apalache. In imperative languages, these properties are usually omitted or
 written as plain-text comments.

 4. We have to introduce a bit of boilerplate, to make Apalache work.

## Step 0: Introducing a template module

*Source files for this step*:
[BinSearch0.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch0.tla).

TLA+ is built around the concept of a state machine. The specified system
starts in a state that is picked from the set of its *initial states*. This
set of states is described with a predicate over states in TLA+. This predicate
is usually called `Init`. Further, the state machine makes a *transition* from
the current state to a successor state. These transitions are described with a
predicate over pairs of states `(current, successor)` in TLA+. This predicate
is usually called `Next`.

We start with the simplest possible specification of a single-state machine.
If we visualize it as a state diagram, it looks like follows:

![Tux, the Linux mascot](./img/single.drawio.svg)

Let's open a new file called `BinSearch0.tla` and type a very minimal module
definition:

```tla
{{#include ../../../test/tla/bin-search/BinSearch0.tla:1:8}}
```

This module does not yet specify any part of the binary search implementation. However, it contains a few important things:

 - It imports constants and operators from three standard modules: `Integers`,
   `Sequences`, and `Apalache`.
 
 - It declares the predicate `Init`. This predicate describes the initial
   states of our state machine. Since we have not declared any variables, it
   defines the single possible state.

 - It declares the predicate `Next`. This predicate describes the transitions
   of our state machine. Again, there are no variables and `Next == TRUE`, so
   this transition defines the entire set of states as reachable in a single
   step.

Now it is a good time to check that Apalache works. Run the following command:   

```sh
$ apalache-mc check BinSearch0.tla
```

The tool output is a bit verbose. Below, you can see the important lines of the
output:

```
...
PASS #13: BoundedChecker
Step 0: picking a transition out of 1 transition(s)
Step 1: picking a transition out of 1 transition(s)
...
Step 10: picking a transition out of 1 transition(s)
The outcome is: NoError
Checker reports no error up to computation length 10
... 
```

We can see that Apalache runs without finding an error, as expected.

If you are curious, replace `TRUE` with `FALSE` in either `Init` or `Next`,
run Apalache again and observe what happens.

It is usually a good idea to start with a spec like `BinSearch0.tla`, to ensure
that the tools are working.

## Step 1: Introducing specification parameters

*Source files for this step*:
[BinSearch1.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch1.tla).

*Diffs*: [BinSearch1.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch1.tla.patch).

The Java code of `binarySearch` accepts two parameters: an array of integers
called `a`, and an integer called `key`. Similar to these parameters, we introduce
two specification parameters (called `CONSTANTS` in TLA+):

 - the input sequence `INPUT_SEQ`, and
 - the element to search for `INPUT_KEY`.

```tla
{{#include ../../../test/tla/bin-search/BinSearch1.tla:1:1}}
{{#include ../../../test/tla/bin-search/BinSearch1.tla:8:18}}
```

Importantly, the constants `INPUT_SEQ` and `INPUT_KEY` are prefixed with type
annotations in the comments:

 - `INPUT_SEQ` has the type `Seq(Int)`, that is, it is a sequence of integers (sequences in TLA+ are indexed), and
 - `INPUT_KEY` has the type `Int`, that is, it is an integer.

Recall that we wanted to specify signed and unsigned Java integers, which are
32 bit long. *TLA+ is not tuned towards any computer architecture.* Its integers
are mathematical integers: always signed and arbitrarily large (unbounded).
To model fixed bit-width integers, we introduce another constant `INT_WIDTH` of
type `Int`:

```tla
{{#include ../../../test/tla/bin-search/BinSearch1.tla:19:22}}
```

The benefit of defining the bit width as a parameter is that we can try
our specification for various bit widths of integers: 4-bit, 8-bit, 16-bit, 32-bit,
etc.  Similar to many programming languages, we introduce several constant
definitions (`a^b` is `a` taken to the power of `b`):

```tla
{{#include ../../../test/tla/bin-search/BinSearch1.tla:24:30}}
```

Note that these definitions do not constrain integers in any way. They are
simply convenient names for the constants that we will need in the
specification.

To make sure that the new specification does not contain syntax errors or
type errors, execute:

```sh
$ apalache-mc check BinSearch1.tla
```

## Step 2: Specifying the base case

*Source files for this step*:
[BinSearch2.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch2.tla).

*Diffs*: [BinSearch2.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch2.tla.patch).

We start with the simplest possible case that occurs in `binarySearch`. Namely,
we consider the case where `low > high`, that is, `binarySearch` never enters
the loop.

**Introduce variables**. To do that, we have to finally introduce some
variables. Obviously, we have to introduce variables `low` and `high`. This is
how we do it:

```tla
{{#include ../../../test/tla/bin-search/BinSearch2.tla:32:38}}
```

The variables `low` and `high` are called *state variables*. They define a state of our state machine. That is, they are never introduced and
never removed. Remember, TLA+ is not tuned towards any particular computer
architecture and thus it does not even have the notion of an execution stack.
You can think of `low` and `high` as being global variables. Yes, global
variables are generally frowned upon in programming languages. However, when dealing with a
specification, they are much easier to reason about than the execution stack.
We will demonstrate how to introduce local definitions later in this tutorial.

We introduce two additional variables, the purpose of which might be less obvious:

```tla
{{#include ../../../test/tla/bin-search/BinSearch2.tla:39:44}}
```

The variable `isTerminated` indicates whether our search has terminated. Why do
we even have to introduce it? Because, some computer systems are not designed
with termination in mind. For instance, such distributed systems as the
Internet and Bitcoin are designed to periodically serve incoming requests
instead of producing a single output for a single input.

If we want to specify the Internet or Bitcoin, do we
understand what it means for them to terminate?

The variable `returnValue` will contain the result of the binary search, when
the search terminates. Recall, there is no execution stack. Hence, we introduce
the variable `returnValue` right away. The downside is that we have to do
book-keeping for this variable.

**Initialize variables.** Having introduced the variables, we have to
initialize them. That is, we want to specify lines 2-3 of the Java code:

```java
1:     public static int binarySearch(int[] a, int key) {
2:         int low = 0;
3:         int high = a.length - 1;
           ...
17:    }
```

To this end, we change the body of the predicate `Init` to the following:

```tla
Init ==
  low = 0 /\ high = Len(INPUT_SEQ) - 1 /\ isTerminated = FALSE /\ returnValue = 0
```

You probably have guessed, what the above line means. Maybe you are a bit
puzzled about the mountain-like operator `/\`. It is called *conjunction*,
which is usually written as `&&` or `and` in programming languages. The
important effect of the above expression is that every variable in the
left-hand side of `=` is required to have the value specified in the right-hand
side of `=`[^assignment-order].

As it is hard to fit many expressions in one line, TLA+ offers special syntax
for writing a big conjunction. Here is the standard way of writing `Init`
(indentation is important):

```tla
{{#include ../../../test/tla/bin-search/BinSearch2.tla:46:51}}
```

The above lines do not deserve a lot of explanation. As you have probably guessed,
`Len(INPUT_SEQ)` computes the length of the input sequence.

[^assignment-order]: It is important to know that TLA+ does not impose any
particular order of evaluation for `/\`. However, both Apalache and TLC
evaluate some expressions of the form `x = e` in the initialization predicate
as assignments.  Hence, it is often a good idea to think about `/\` as being
evaluated from left to right.

**Update variables.** Having done all the preparatory work, we are now ready to
specify the behavior in lines 5 and 16 of `binarySearch`.

```java
1:     public static int binarySearch(int[] a, int key) {
2:         int low = 0;
3:         int high = a.length - 1;
4:
5:         while (low <= high) {
            ...
15:        }
16:        return -(low + 1);  // key not found.
17:    }
```

To this end, we redefine `Next` as follows:

```tla
{{#include ../../../test/tla/bin-search/BinSearch2.tla:53:62}}
```

Most likely, you have no problem reading this definition, except for the part
that includes `isTerminated'`, `returnValue'`, and `UNCHANGED`. Recall that a
transition predicate, like `Next`, specifies the relation between two states of
the state machine; the current state, the variables of which are referenced by
unprimed names, and the successor-state, the variables of which are referenced
by primed names.

The expression `isTerminated' = TRUE` means that only states where
`isTerminated` equals `TRUE` can be successors of the current state. In
general, `isTerminated'` could also depend on the value of `isTerminated`, but
here, it does not. Likewise, `returnValue' = -(low + 1)` means that
`returnValue` has the value `-(low + 1)` in the next state. The expression
`UNCHANGED <<low, high>>` is a convenient shortcut for writing `low' = low /\
high' = high`.  Readers unfamiliar with specification languages might question
the purpose of `UNCHANGED`, since in most programming languages variables only
change when they are explicitly changed.  However, a transition predicate, like
`Next`, establishes a relation between pairs of states.  If we were to omit
`UNCHANGED`, this would mean that we consider states in which `low` and `high`
have _completely arbitrary_ values as valid successors.  This is clearly not
how Java code should behave.  To encode Java semantics, we must therefore
explicitly state that `low` and `high` do not change in this step.

It is important to understand that an expression like `returnValue' = -(low +
1)` *does not immediately update* the variable on the left-hand side. Hence,
`returnValue` still refers to the value in the state before evaluation of
`Next`, whereas `returnValue'` refers to the value in the state that is
computed after evaluation of `Next`. You can think of the effect of `x' = e`
being delayed until the whole predicate `Next` is evaluated.

## Step 2b: Basic checks for the base case

*Source files for this step*:
[BinSearch2.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch2.tla)
and
[MC2_8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC2_8.tla).

As we discussed, it is a good habit to periodically run the model checker, as you are writing
the specification. Even if it doesn't check much, you would be able to catch
the moment when the model checker slows down. This may give you a useful
hint about changing a few things before you have written too much code.

Let us check `BinSearch2.tla`:

```sh
$ apalache-mc check BinSearch2.tla
```

If it is your first TLA+ specification, you may be surprised by this error:

```
...
PASS #13: BoundedChecker
This error may show up when CONSTANTS are not initialized.
Check the manual: https://apalache.informal.systems/docs/apalache/parameters.html
Input error (see the manual): SubstRule: Variable INPUT_SEQ is not assigned a value
...
```

Apalache complains that we have declared several constants (`INPUT_SEQ`,
`INPUT_KEY`, and `INT_WIDTH`), but we have never defined them.

**Adding a model file.** The standard approach in this case is either to fix
all constants, or to introduce another module that
fixes the parameters and instantiates the general specification. Although
Apalache supports [TLC Configuration Files][], for the purpose of this tutorial,
we will stick to tool-agnostic TLA+ syntax.

To this end, we add a new file `MC2_8.tla` with the following contents:

```tla
{{#include ../../../test/tla/bin-search/MC2_8.tla}}
```

As you can see, we fix the values of all parameters. We are instantiating
the module `BinSearch2` with these fixed parameters. Since instantiation
requires all constants and variables to be defined, we copy the variables
definitions from `BinSearch2.tla`.

Since we are fixing the parameters with concrete values, `MC2_8.tla` looks very
much like a unit test. It's a good start for debugging a few things, but since
our program is entirely sequential, our specification is as good as a unit
test. Later in this tutorial we will show how to leverage Apalache to check
properties for all possible inputs (up to some bound).

Let us check `MC2_8.tla`:

```sh
$ apalache-mc check MC2_8.tla
...
Checker reports no error up to computation length 10
```

This time Apalache has not complained. This is a good time to stop and think
about whether the model checker has told us anything interesting. Kind of. It
told us that it has not found any contradictions. But it did not tell us
anything interesting about our expectations. Because we have not set our
expectations yet!

## Step 3: Specifying an invariant and checking it for the base case

*Source files for this step*:
[BinSearch3.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch3.tla)
and
[MC3_8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC3_8.tla).

*Diffs*:
[BinSearch3.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch3.tla.patch)
and
[MC3_8.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC3_8.tla.patch).

What do we expect from binary search? We can check the Java documentation,
e.g., [Arrays.java in OpenJDK][]:

> ...the return value will be >= 0 if and only if the key is found.

This property is actually quite easy to write in TLA+. First, we
introduce the property that we call `ReturnValueIsCorrect`:

```tla
{{#include ../../../test/tla/bin-search/BinSearch3.tla:71:83}}
```

Let us decompose this property into smaller pieces. First, we define the set
`MatchingIndices`:

```tla
{{#include ../../../test/tla/bin-search/BinSearch3.tla:75:77}}
```

With this TLA+ expression we define a *local constant* called `MatchingIndices`
that is equal to the set of indices `i` in `INPUT_SEQ` so that the sequence
elements at these indices are equal to `INPUT_KEY`. If this syntax
is hard to parse for you, here is how we could write a similar definition in a
functional programming language (Scala):

```scala
val MatchingIndices =
    INPUT_SEQ.indices.toSet.filter { i => INPUT_SEQ(i) == INPUT_KEY }
```

Since the
sequence indices in TLA+ start with 1, we require that `returnValue + 1`
belongs to `MatchingIndices` when `MatchingIndices` is non-empty. If
`MatchingIndices` is empty, we require `returnValue` to be negative.

We can check that the property `ReturnValueIsCorrect` is an *invariant*, that
is, it holds in every state that is reachable from the states specified by `Init`
via a sequence of transitions specified by `Next`:

```sh
$ apalache-mc check --inv=ReturnValueIsCorrect MC3_8.tla
```

This property is violated in the initial state. To see why, check the file
`counterexample1.tla`.

Actually, we only expect this property to hold after the computation terminates,
that is, when `isTerminated` equals to `TRUE`. Hence, we add the following
invariant:

```tla
{{#include ../../../test/tla/bin-search/BinSearch3.tla:84:86}}
```

**Digression: Boolean connectives.** In the above code, the operator `=>` is
the [Classical implication][]. In general, `A => B` is equivalent to `IF A THEN
B ELSE TRUE`. The implication `A => B` is also equivalent to the TLA+
expression `~A \/ B`, which one can read as "not A holds, or B holds". The
operator `\/` is called *disjunction*. As a reminder, here is the standard
truth table for the Boolean connectives, which are no different from the
Boolean logic in TLA+:

| `A`     | `B`     | `~A`    | `A \/ B` | `A /\ B` | `A => B` |
| ------- | ------- | ------- | -------- | -------- | -------- |
| `FALSE` | `FALSE` | `TRUE`  | `FALSE`  | `FALSE`  | `TRUE`   |
| `FALSE` | `TRUE`  | `TRUE`  | `TRUE`   | `FALSE`  | `TRUE`   |
| `TRUE`  | `FALSE` | `FALSE` | `TRUE`   | `FALSE`  | `FALSE`  |
| `TRUE`  | `TRUE`  | `FALSE` | `TRUE`   | `TRUE`   | `TRUE`   |

**Checking Postcondition.**
Let us check `Postcondition` on `MC3_8.tla`:

```sh
$ apalache-mc check --inv=Postcondition MC3_8.tla
```

This property holds true. However, it's a small win, as `MC3_8.tla` fixes all
parameters. Hence, we have checked the property just for one data point. In
Step 5, we will check `Postcondition` for all sequences admitted by `INT_WIDTH`.

## Step 4: Specifying the loop (with a caveat)

*Source files for this step*:
[BinSearch4.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch4.tla)
and
[MC4_8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC4_8.tla).

*Diffs*:
[BinSearch4.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch4.tla.patch)
and
[MC4_8.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC4_8.tla.patch).

We specify the loop of `binarySearch` in TLA+ as follows:

```tla
{{#include ../../../test/tla/bin-search/BinSearch4.tla:55:77}}
```

Let's start with these two definitions:

```tla
{{#include ../../../test/tla/bin-search/BinSearch4.tla:60:61}}
```

As you have probably guessed, we define two (local) values `mid` and `midVal`.
The value `mid` is the average of `low` and `high`. The operator `\div` is
simply integer division, which is usually written as `/` or `//` in programming
languages. The value `midVal` is the value at the location `mid + 1`. Since
the TLA+ sequence `INPUT_SEQ` has indices in the range `1..Len(INPUT_SEQ)`,
whereas we are computing zero-based indices, we are adjusting the index by one,
that is, we write `INPUT_SEQ[mid + 1]` instead of `INPUT_SEQ[mid]`.

*Warning: The definitions of `mid` and `midVal` do not properly reflect the
Java code of `binarySearch`. We will fix them later. It is a good exercise
to stop here and think about the source of this imprecision.*

The following lines look like ASCII graphics, but by now you should know
enough to read them:

```tla
{{#include ../../../test/tla/bin-search/BinSearch4.tla:60:71}}
```

These lines are the indented form of `\/` for three cases:

 - when `midVal < INPUT_KEY`, or
 - when `midVal > INPUT_KEY`, or
 - when `midVal = INPUT_KEY`.

We could write these expressions with `IF-THEN-ELSE` or even with the TLA+
operator `CASE` (see [Summary of TLA+][]). However, we find the disjunctive
form to be the least cluttered, though unusual.

Now we can check the postcondition again:

```sh
$ apalache-mc check --inv=Postcondition MC4_8.tla
```

The check goes through, but did it do much? Recall, that we fixed `INPUT_SEQ`
to be the empty sequence `<< >>` in `MC4_8.tla`. Hence, we never enter the loop
we have just specified.

Actually, Apalache gives us a hint that it never tries some of the
cases:

```
...
PASS #13: BoundedChecker
State 0: Checking 1 state invariants
Step 0: picking a transition out of 1 transition(s)
Step 1: Transition #0 is disabled
Step 1: Transition #1 is disabled
Step 1: Transition #2 is disabled
Step 1: Transition #3 is disabled
State 1: Checking 1 state invariants
Step 1: picking a transition out of 1 transition(s)
Step 2: Transition #0 is disabled
Step 2: Transition #1 is disabled
Step 2: Transition #2 is disabled
Step 2: Transition #4 is disabled
Step 2: picking a transition out of 1 transition(s)
...
```

**Digression: symbolic transitions.** Internally, Apalache decomposes the
predicates `Init` and `Next` into independent pieces like `Init == Init$0 \/
Init$1` and `Next == Next$0 \/ Next$1 \/ Next$2 \/ Next$3`. If you want to see
how it is done, run Apalache with the options `--write-intermediate` and `--run-dir`:

```sh
$ apalache-mc check --inv=Postcondition --write-intermediate=1 --run-dir=out MC4_8.tla
```

Check the file `out/intermediate/XX_OutTransitionFinderPass.tla`, which contains the
preprocessed specification that has `Init` and `Next` decomposed. You can find
a detailed explanation in the section on [Assignments in Apalache][].

## Step 5: Checking Postcondition for plenty of inputs

*Source files for this step*:
[BinSearch5.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch5.tla)
and
[MC5_8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC5_8.tla).

*Diffs*:
[BinSearch5.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch5.tla.patch)
and
[MC5_8.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC5_8.tla.patch).

In this step, we are going to check the invariant `Postcondition` for all
possible input sequences and all input keys (for a fixed bit-width).

Create the file `MC5_8.tla` with the following contents:

```tla
{{#include ../../../test/tla/bin-search/MC5_8.tla::34}}
==================
```

Note that we introduced `INPUT_SEQ` and `INPUT_KEY` as parameters again. We
cannot check `MC5_8.tla` just like that. If we try to check `MC5_8.tla`,
Apalache would complain again about a value missing for `INPUT_SEQ`.

To check the invariant for all sequences, we will use two advanced features
of Apalache: [ConstInit predicate][] and [Value generators][].

**ConstInit.** This idiom allows us to initialize `CONSTANTS` with a TLA+
formula. Let us introduce the following operator definition in `MC5_8.tla`:

```tla
ConstInit ==
    /\ INPUT_KEY \in Int
    \* Seq(Int) is a set of all sequences that have integers as elements
    /\ INPUT_SEQ \in Seq(Int) 
```

This is straightforward definition. However, it does not work in Apalache:

```sh
$ apalache-mc check --cinit=ConstInit --inv=Postcondition MC5_8.tla
...
MC5_8.tla:39:22-39:29: unsupported expression: Seq(_) produces an infinite set of unbounded sequences.
Checker has found an error
...
```

The issue with our definition of `ConstInit` is that it requires the model
checker to reason about the infinite set of sequences, namely, `Seq(Int)`.
Interestingly, the model checking does not complain about the expression
`INPUT_KEY \in Int`. The reason is that this expression requires the model
checker to reason about one integer, though it ranges over the infinite set of
integers.

**Value generators.** Fortunately, this problem can be easily circumvented by
using Apalache [Value generators][][^generators].


Let us rewrite `ConstInit` in `MC5_8.tla` as follows:

```tla
ConstInit ==
    /\ INPUT_KEY = Gen(1)
    /\ INPUT_SEQ = Gen(MAX_INT)
```

In this new version, we use the Apalache operator `Gen` to:

  - produce an unrestricted integer to be used as a value of `INPUT_KEY` and
  - produce a sequence of integers to be used as a value of `INPUT_SEQ`. This
    sequence is unrestricted, except its length is bounded with `MAX_INT`,
    which is exactly what we need in our case study.

The operator `Gen` introduces a data structure of proper type whose size is
bounded with the argument of `Gen`. For instance, the type of `INPUT_SEQ` is
the sequence of integers, and thus `Gen(MAX_INT)` produces an unrestricted
sequence of up to `MAX_INT` elements. This sequence is bound to the name
`INPUT_SEQ`. For details, see [Value generators][]. This lets Apalache check
all instances of the data structure, without enumerating the instances!

By doing so, we are able to check the specification for all the inputs, when we
fix the bit width. To quickly get feedback from Apalache, we fix `INT_WIDTH` to 8 in the model `MC5_8.tla`.

[^generators]: If you know property-based testing, e.g., [QuickCheck][],
Apalache generators are inspired by this idea. In contrast to property-based
testing, an Apalache generator is not randomly producing values. Rather,
Apalache simply introduces an unconstrained data structure (e.g., a set, a
function, or a sequence) of the proper type. Hence, Apalache is reasoning about
all possible instances of this data structure, instead of reasoning about a
small set of randomly chosen instances.

Let us check `Postcondition` again:

```sh
$ apalache-mc check --cinit=ConstInit --inv=Postcondition MC5_8.tla
...
State 2: state invariant 0 violated. Check the counterexample in: 
  /[a long path]/counterexample1.tla
...
```

Let us inspect the counterexample:

```tla
---------------------------- MODULE counterexample ----------------------------  
EXTENDS MC5_8

(* Constant initialization state *)
ConstInit == INPUT_KEY = -1 /\ INPUT_SEQ = <<0, -1>>

(* Initial state *)
State0 ==
  INPUT_KEY = -1
    /\ INPUT_SEQ = <<0, -1>>
    /\ high = 1
    /\ isTerminated = FALSE
    /\ low = 0
    /\ returnValue = 0

(* Transition 1 to State1 *)
State1 ==
  INPUT_KEY = -1
    /\ INPUT_SEQ = <<0, -1>>
    /\ high = -1
    /\ isTerminated = FALSE
    /\ low = 0
    /\ returnValue = 0

(* Transition 3 to State2 *)
State2 ==
  INPUT_KEY = -1
    /\ INPUT_SEQ = <<0, -1>>
    /\ high = -1
    /\ isTerminated = TRUE
    /\ low = 0
    /\ returnValue = -1
...
```

Is it a real issue? It is, but it is not the issue of
the search, rather our invariant `Postcondition` is imprecise.

## Step 5b: Fixing the postcondition

*Source files for this step*:
[BinSearch5.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch5.tla)
and
[MC5_8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC5_8.tla).

If we check our source of truth, that is, the Java documentation in
[Arrays.java in OpenJDK][], we will see the following sentences:

    The range must be sorted (as by the {@link #sort(int[], int, int)} method)
    prior to making this call. If it is not sorted, the results are undefined.
    If the range contains multiple elements with the specified value, there is
    no guarantee which one will be found.

It is quite easy to add this constraint [^no-pre]. This is where TLA+ starts to
shine:

```tla
{{#include ../../../test/tla/bin-search/BinSearch5.tla:80:88}}
...
{{#include ../../../test/tla/bin-search/BinSearch5.tla:109:112}}
```

If we check `PostconditionSorted`, we do not get any error after 10 steps:

```sh
$ apalache-mc check --cinit=ConstInit --inv=PostconditionSorted MC5_8.tla
...
The outcome is: NoError
Checker reports no error up to computation length 10
```

It takes some time to explore all executions of length up to 10 steps, for all
input sequences of length up to `2^7 - 1` arbitrary integers. If we think about
it, the model checker managed to crunch infinitely many numbers in several
hours. Not bad.

*Exercise.* If you are impatient, you can check `PostconditionSorted` for the
configuration that has integer width of 4 bits. It takes only a few seconds to
explore all executions.

[^no-pre]: Instead of checking whether `INPUT_SEQ` is sorted in the
post-condition, we could restrict the constant `INPUT_SEQ` to be sorted in
every execution. That would effectively move this constraint into the
pre-condition of the search. Had we done that, we would not be able to observe
the behavior of the search on the unsorted inputs. An important property is
whether the search is terminating on all inputs.

## Step 6: Checking termination and progress

*Source files for this step*:
[BinSearch6.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch6.tla)
and
[MC6_8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC6_8.tla).

*Diffs*:
[BinSearch6.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch6.tla.patch)
and
[MC6_8.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC6_8.tla.patch).

Actually, we do not need 10 steps to check termination for the case `INT_WIDTH
= 8`. If you recall the complexity of the binary search, it needs
`ceil(log2(Len(INPUT_SEQ)))` steps to terminate.

To check this property, we add the number of steps as a variable in
`BinSearch6.tla` and in `MC6_8.tla`:

```tla
VARIABLES
    ...
    \* The number of executed steps.
    \* @type: Int;
    nSteps
```

Also, we update `Init` and `Next` in `BinSearch6.tla` as follows:

```tla
Init ==
    ...
    /\ nSteps = 0

Next ==
    IF ~isTerminated
    THEN IF low <= high
      THEN          \* lines 6-14
        /\ nSteps' = nSteps + 1
        /\ LET mid == (low + high) \div 2 IN
         ...
      ELSE          \* line 16
        /\ isTerminated' = TRUE
        /\ returnValue' = -(low + 1)
        /\ UNCHANGED <<low, high, nSteps>>
    ELSE            \* isTerminated
      UNCHANGED <<low, high, returnValue, isTerminated, nSteps>>
```

Having `nSteps`, we can write the `Termination` property:

```tla
\* We know the exact number of steps to show termination.
Termination ==
    (nSteps >= INT_WIDTH) => isTerminated
```

Let us check `Termination`:

```sh
$ apalache-mc check --cinit=ConstInit --inv=Termination MC6_8.tla
...
Checker reports no error up to computation length 10
It took me 0 days  0 hours  0 min 19 sec
```

Even if did not know precisely complexity of the binary search, we could
write a simpler property, which demonstrates progress of the search:

```tla
Progress ==
    ~isTerminated' => (low' > low \/ high' < high)
```

It takes about 10 seconds to check `Progress` as well.

## Step 7: Fixed-width integers

*Source files for this step*:
[BinSearch7.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch7.tla)
and
[MC7_8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC7_8.tla).

*Diffs*:
[BinSearch7.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch7.tla.patch)
and
[MC7_8.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC7_8.tla.patch).

Do you recall that our specification of the loop had a caveat? Let us have a
look at this piece of the specification again:

```tla
{{#include ../../../test/tla/bin-search/BinSearch6.tla:63:78}}
```

You can see that all arithmetic operations are performed over TLA+ integers,
that is, unbounded integers. We have to implement fixed-width integers ourselves.
Fortunately, we do not have to implement the whole set of integer operators,
but only the addition over signed integers, which has a potential to overflow.
To this end, we have to recall how signed integers are represented in modern
computers, see [Two's complement][]. Fortunately, we do not have to worry about
an efficient implementation of integer addition. We simply use addition over
unbounded integers to implement addition over fixed-width integers:

```tla
{{#include ../../../test/tla/bin-search/BinSearch7.tla:54:65}}
```

Having defined `IAdd`, we replace addition over unbounded integers with `IAdd`:

```tla
{{#include ../../../test/tla/bin-search/BinSearch7.tla:76:93}}
        ...
```

This finally gives us a specification that faithfully represents the Java code
of `binarySearch`. Now we can check all expected properties once again:

```sh
$ apalache-mc check --cinit=ConstInit --inv=PostconditionSorted MC7_8.tla
...
State 2: state invariant 0 violated.
...
Total time: 2.786 sec
```

```sh
$ apalache-mc check --cinit=ConstInit --inv=Progress MC7_8.tla
...
State 1: action invariant 0 violated.
...
Total time: 2.935 sec
```

```sh
$ apalache-mc check --cinit=ConstInit --inv=Termination MC7_8.tla
...
State 8: state invariant 0 violated.
...
Total time: 39.540 sec
```

As we can see, all of our invariants are violated. They all demonstrate the
issue that is caused by the integer overflow!

## Step 8: Checking the boundaries

*Source files for this step*:
[BinSearch8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch8.tla)
and
[MC8_8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC8_8.tla).

*Diffs*:
[BinSearch8.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch8.tla.patch)
and
[MC8_8.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC8_8.tla.patch).

As we have seen in Step 7, the cause of all errors in `PostconditionSorted`,
`Termination`, and `Progress` is that the addition `low + high` overflows and
thus the expression `INPUT_SEQ[mid + 1]` accesses `INPUT_SEQ` outside of its
domain.

Why did Apalache not complain about access outside of the domain? Its behavior
is actually consistent with [Specifying Systems][] (p. 302):

> A function *f* has a domain DOMAIN *f*, and the value of *f*[*v*] is
> specified only if *v* is an element of DOMAIN *f*.

Hence, Apalache returns some value of a proper type, if `v` is outside of
`DOMAIN f`. As we have seen in Step 7, such a value would usually show up in a
counterexample. In the future, Apalache will probably have an automatic check
for out-of-domain access. For the moment, we can write such a check as a state
invariant. By propagating the conditions from `INPUT_SEQ[mid + 1]` up in `Next`,
we construct the following invariant:


```tla
{{#include ../../../test/tla/bin-search/BinSearch8.tla:144:150}}
```

Apalache finds a violation of this invariant in a few seconds:

```
$ apalache-mc check --cinit=ConstInit --inv=InBounds MC8_8.tla
...
State 1: state invariant 0 violated.
...
Total time: 3.411 sec
```

If we check `counterexample1.tla`, it contains the following values for `low`
and `high`:

```
State0 ==
    /\ high = 116
    /\ low = 0
    ...

State1 ==
    /\ high = 116
    /\ low = 59
    ...
```

In state 1, we have `low + high = 116 + 59 > 2^7`. Since we have `INT_WIDTH
= 8`, we have `IAdd(116, 59) = -81`.

## Step 9: Fixing the access bug

*Source files for this step*:
[BinSearch9.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch9.tla)
and
[MC9_8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC9_8.tla).

*Diffs*:
[BinSearch9.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch9.tla.patch)
and
[MC9_8.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC9_8.tla.patch).

Let us apply the fix that was proposed by Joshua Bloch in [Nearly All Binary
Searches and Mergesorts are Broken][]. Namely, we update this line of
`BinSearch8.tla`:

```tla
{{#include ../../../test/tla/bin-search/BinSearch8.tla:82:83}}
```

The fix is as follows:

```tla
{{#include ../../../test/tla/bin-search/BinSearch9.tla:83:84}}
```

We also update `InBounds` as follows:

```tla
{{#include ../../../test/tla/bin-search/BinSearch9.tla:145:147}}
...
```

Now we check the four invariants: `InBounds`, `PostconditionSorted`,
`Termination`, and `Progress`.

```sh
$ apalache-mc check --cinit=ConstInit --inv=InBounds MC9_8.tla
...
The outcome is: NoError
...
Total time: 76.352 sec
```

```sh
$ apalache-mc check --cinit=ConstInit --inv=Progress MC9_8.tla
...
The outcome is: NoError
...
Total time: 63.578 sec
```

```sh
$ apalache-mc check --cinit=ConstInit --inv=Termination MC9_8.tla
...
The outcome is: NoError
...
Total time: 72.682 sec
```

```sh
$ apalache-mc check --cinit=ConstInit --inv=PostconditionSorted MC9_8.tla
...
The outcome is: NoError
...
Total time: 2154.646 sec
```

*Exercise:* It takes quite a bit of time to check `PostconditionSorted`.
Change `INT_WIDTH` to 6 and check all these invariants once again. Observe that
it takes Apalache significantly less time.

*Exercise:* Change `INT_WIDTH` to 16 and check all these invariants once again.
Observe that it takes Apalache significantly more time.

## Step 10: Beautifying the specification

*Source files for this step*:
[BinSearch10.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch10.tla)
and
[MC10_8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC10_8.tla).

*Diffs*:
[BinSearch10.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch10.tla.patch)
and
[MC10_8.tla.patch](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC10_8.tla.patch).

We have reached our goals: TLA+ and Apalache helped us in finding the access
bug and showing that its fix works. Now it is time to look back at the
specification and make it easier to read.

Let us have a look at our definition of `Next`:

```tla
{{#include ../../../test/tla/bin-search/BinSearch9.tla:77:100}}
```

`Next` contains a massive expression. We can decompose it nicely in smaller
pieces:

```tla
{{#include ../../../test/tla/bin-search/BinSearch10.tla:78:113}}
```

The definitions `LoopIteration`, `LoopExit`, and `StutterOnTermination` are
called actions in TLA+. It is usually a good idea to decompose a large `Next`
formula into actions. Normally, an action contains assignments to all primed
variables.

## Discussion

The final specifications can be found in
[BinSearch10.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/BinSearch10.tla)
and
[MC10_8.tla](https://github.com/informalsystems/apalache/blob/main/test/tla/bin-search/MC10_8.tla).

In this tutorial we have shown how to:

 - Specify the behavior of a sequential algorithm (binary search).
 - Specify invariants that check safety and termination.
 - Take into account the specifics of a computer architecture (fixed bit
   width).
 - Automatically find examples of simultaneous invariant violation.
 - Efficiently check the expected properties against our specification.

We have written our specification for parameterized bit width. This lets us
check the invariants relatively quickly and get fast feedback from the model
checker. We chose a bit width of 8, a non-trivial value for which
Apalache terminates within reasonable time. Importantly, the specification
for the bit width of 32 stays the same; we only have to change `INT_WIDTH`. Of
course, Apalache reaches its limits when we set `INT_WIDTH` to 16 or 32. In
these cases, it has to reason about all sequences of length up to 32,767
elements or 2 Billion elements, respectively!

Apalache gives us a good idea whether the properties of our
binary search specification hold true. However, it does not give us an ultimate proof of correctness for
Java integers. If you need such a proof, you should probably use TLAPS. Check
the paper on [Proving Safety Properties][] by Leslie Lamport.

This tutorial is rather long. This is because we wanted to show the evolution
of a TLA+ specification, as we were writing it and checking it with Apalache.
There are many different styles of writing TLA+ specifications. One of our
goals was to demonstrate the incremental approach to specification writing. In
fact, this approach is not very different from incremental development of
programs in the spirit of [Test-driven development][]. It took us 2-3 hours to
iteratively develop a specification that is similar to the one demonstrated in
this tutorial.

This tutorial touches upon the basics of TLA+ and Apalache. For instance, we
did not discuss non-determinism, as our specification is entirely
deterministic. We will demonstrate advanced features in future tutorials.

If you are experiencing a problem with Apalache, feel free to [open an issue]
or drop us a message on [Zulip chat].


[HOWTO on writing type annotations]: ../HOWTOs/howto-write-type-annotations.md
[Apalache installation]: ../apalache/installation/index.md
[Leslie Lamport]: https://lamport.azurewebsites.net/
[open an issue]: https://github.com/informalsystems/apalache/issues
[TLC Configuration Files]: ../apalache/parameters.md#tlc-configuration-file
[Tutorial on Snowcat]: ./snowcat-tutorial.md
[Nearly All Binary Searches and Mergesorts are Broken]: https://ai.googleblog.com/2006/06/extra-extra-read-all-about-it-nearly.html
[Binary search in ProB]: https://groups.google.com/g/tlaplus/c/msLltIcexF4/m/qnABiKJmDgAJ
[Binary search with a TLAPS proof]: https://github.com/tlaplus/Examples/blob/master/specifications/LoopInvariance/BinarySearch.tla
[Proving Safety Properties]: http://lamport.azurewebsites.net/tla/proving-safety.pdf
[Binary search algorithm]: https://en.wikipedia.org/wiki/Binary_search_algorithm
[CBMC]: https://www.cprover.org/cbmc/
[Coral]: https://www.microsoft.com/en-us/research/project/q-program-verifier/
[Stainless]: https://stainless.epfl.ch/
[TLA+ Cheatsheet in HTML]: https://mbt.informal.systems/docs/tla_basics_tutorials/tla+cheatsheet.html
[Summary of TLA+]: https://lamport.azurewebsites.net/tla/summary-standalone.pdf
[TLA+ Video Course]: http://lamport.azurewebsites.net/video/videos.html
[Classical implication]: https://en.wikipedia.org/wiki/Material_conditional
[Assignments in Apalache]: ../apalache/assignments-in-depth.md
[ConstInit predicate]: ../apalache/parameters.md#constinit-predicate
[Value generators]: ../lang/apalache-operators.md#value-generators
[QuickCheck]: https://en.wikipedia.org/wiki/QuickCheck
[Arrays.java in OpenJDK]: https://github.com/openjdk/jdk/blob/d7f31d0d53bfec627edc83ceb75fc6202891e186/src/java.base/share/classes/java/util/Arrays.java#L1662-L1698
[Two's complement]: https://en.wikipedia.org/wiki/Two%27s_complement
[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=learning.html
[Test-driven development]: https://en.wikipedia.org/wiki/Test-driven_development
[TLC]: https://github.com/tlaplus/tlaplus/
[Zulip chat]: https://informal-systems.zulipchat.com/login/#narrow/stream/265309-apalache
[ZIP archive]: https://download-directory.github.io/?url=https://github.com/informalsystems/apalache/tree/main/test/tla/bin-search
