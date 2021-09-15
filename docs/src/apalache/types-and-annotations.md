## Old type inference and type annotations (prior to version 0.15.0)

**WARNING:** This page is describing old type annotations, which were used
in Apalache prior to version 0.15.0.

We have recently implemented a new type checker called Snowcat.
See the [chapter in the manual](./typechecker-snowcat.md).
Snowcat is user-friendly and much smarter than the current trivial type
checker.  To get the idea about the new type checker, see [the talk at TLA+
Community Meeting 2020](https://youtu.be/hnp25hmCMN8). We are preparing a
tutorial on the new typechecker. The old type annotations are replaced with
the new annotations as documented in [ADR002](../adr/002adr-types.md)
and [ADR004](../adr/004adr-annotations.md).

---------------------------------------------------------------------------------

### Do I use the old type annotations?

You can easily check, whether the old type annotations are used in your specification.
Simply, search for the following declaration:

```tla
a <: b == a
```

If your specification contains such a declaration and it is used somewhere,
then you are using the old type annotations. You have to remove them and write
the new ones.  The old and new type annotations are conceptually different, so there is
no automatic upgrade process.

### Description of the old type annotations

Our model checker assigns types to variables, in order to encode TLA+ expressions
in [Z3](https://github.com/Z3Prover/z3). Hence, the expressions that are ill-typed
(from the point of view of our type system), will be rejected right away. Some
expressions, such as ``{}`` and ``<<>>`` require an advanced type inference algorithm,
so the model checker will ask the user to provide the tool with a type annotation.
To get an idea of our type system, check Section 2. In a nutshell,
if a TLA+ expression cannot be decorated with a type annotation,
it is not supported _yet_. Exception is made for non-recursive TLA+ operators, as they are
expanded before the type inference is run.

### 1. Type inference

Starting with the version `0.4.0` (and ending with version `0.11.0`),
our model checker runs the naive type
inference algorithm for every computation step:

 1. It assumes that all operator definitions have been replaced with their
bodies. (This is done automatically by Apalache.)

 1. It assumes that non-primed variables have been assigned types already.
 As expected, the non-primed variables get their initial types by running
 type inference on ``Init``.

 1. It recursively computes the types of subexpressions in a TLA+ expression in
 a bottom-up way as follows:

    1. A literal is assigned the respective basic type. That is, an integer,
     a Boolean, or a string gets assigned the integer, Boolean, or the constant
     type respectively.
    1. An assignment-like expression ``x' = e`` or ``x' \in S`` assigns to ``x'``
     the type of ``e`` and the type of ``S`` elements respectively. The type
     checker requires that ``x'`` is assigned the same type across all formula
     branches. However, variables _may_ have different types at different steps.
     For instance, the definitions ``Init == x = 1`` and ``Next == x' = {x}``
     will be processed perfectly fine: ``x`` is assigned the type ``Int`` in the initial
     states, and the type ``Set(...(Set(Int)))`` of _n_ nested sets at the _n_-th step, ``n >= 0``.
    1. The expressions that introduce bound variables, e.g., ``{e: x \in S}``,
    are treated as usual: first, the type of ``S`` is computed and ``x`` is assigned
    the element type, and then the type of ``e`` is computed, which immediately
    gives us the type of the set expression.

This approach manages to automatically compute types of many TLA+ expressions.
However, there a few problematic cases that require type annotations:

 1. An empty set ``{}`` gets assigned the type ``Set[Unknown]``. When it is later
 combined with a more precise type, e.g., as in ``{} \union {1}``, the type finder
 reports a type error. In this case, the user has to write a type annotation.
 For instance, the above-mentioned problematic expression can be fixed as follows:
 ``({} <: {Int}) \union {1}``.
 1. Similar to an empty set, an empty sequence ``<<>>`` gets assigned the type
  ``Seq[Unknown]``. Hence ``<<>> \o <<1>>`` produces a type error. To resolve this,
  the user has to write a type annotation ``(<<>> <: Seq(Int)) \o <<1>>``.
 1. It is common to mix records that have different sets of fields, e.g.,
  see [Paxos](https://github.com/tlaplus/Examples/tree/master/specifications/Paxos).
  However, our type checker will report a type error on the following expression:
  ``{[type |-> "1a", bal |-> 1]} \union {[type |-> "2a", bal |-> 2, val |-> 3]}``.
  To resolve this, the user has to write a type annotation:
   ``{[type |-> "1a", bal |-> 1] <: MT} \union {[type |-> "2a", bal |-> 2, val |-> 3]}``,
   where ``MT`` is defined as ``[type |-> STRING, bal |-> Int, val |-> Int]``.
  The type checker requires that the fields with the same name are assigned
  the same type.

### 2. Type annotations

As there is no standard way of specifying types in TLA+ (hey, it is untyped by design),
we introduce a simple convention to specify types by writing special TLA+ expressions.

As a preliminary step, the user has to introduce the operator ``<:`` as follows:

```tla
a <: b == a
```

This operator does not nothing else but returns its first argument, so the standard TLA+
tools will ignore the second argument, which contains a type annotation. Our model checker
interprets the second argument of the operator ``<:`` as a type annotation.
(This also means that you should not assign any other meaning to ``<:`` in your specifications.)

Further, the user may use ``<:`` to define types of problematic expressions, see the
examples in Section 1.

The syntax for type annotations is given below. Note that these expressions should not be
understood as sets of values, as one would expects from type invariants such as ``TypeOK``. Rather,
they are TLA+ expressions that are parsed by the model checker, in order to construct types.

The syntax of type annotations is as follows:

  1. ``Int`` specifies the integer type. For instance, ``x <: Int`` specifies that ``x``
  is an integer, but not a set of integers.
  1. ``BOOLEAN`` specifies the Boolean type. Again, although we are using a set here,
  its purpose is to say that an expression is a Boolean, not a set of Booleans.
  1. ``STRING`` specifies the type of constants, e.g., ``"a"`` and ``"hello"``
  are such constants.
  1. ``{T}`` specifies the set whose elements have type ``T``. For instance,
  ``{Int}`` specifies a set of integers, whereas ``{{BOOLEAN}}`` specifies
  a set of sets of Booleans. Note that you should always use singleton sets in
  type annotations. For instance, ``{Int, BOOLEAN}`` would be immediately rejected.
  Hence, sets should contain the elements of the same type (there is some flexibility
  for records, see Section 1)
  1. ``[T_1 -> T_2]`` specifies the type of a function whose arguments have type ``T_1``,
  and the results are of type ``T_2``. Hence, a function should return the values
  of the same type.
  1. ``<<T_1, ..., T_k>>`` specifies the type of a _k_-element tuple whose
  elements have types ``T_1, ..., T_k`` respectively. Note that different fields
  of a tuple are allowed to have different types. In these sense, we differentiate them
  from the general functions.
  1. ``[f_1 |-> T_1, ..., f_k |-> T_k]`` specifies the type of a _k_-field record,
  whose field ``f_i`` is of the type ``T_i``. The types ``T_1, ..., T_k`` may differ. Again,
  that makes them different from the general functions.
  1. ``Seq(T)`` specifies the type of finite sequences, whose elements are of type ``T``.
  There are no restrictions on the sequence length, except finiteness. In theory,
  a sequence of type ``Seq[T]`` is no different from a function of type ``[Int -> T]``.
  In practice, we use different encodings for the general functions and sequences.

