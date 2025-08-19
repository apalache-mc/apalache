# Variants

[[Back to Apalache extensions]](./apalache-extensions.md)

[Variants][] (also called *tagged unions* or *sum types*) are useful, when you want to combine
values of different shapes in a single set or a sequence.

**Idiomatic tagged unions in untyped TLA+.**
In untyped TLA+, one can construct sets, which contain records with different fields,
where one filed is typically used as a disambiguation tag. 
For instance, we could create a set that contains two records of different shapes:

```tla
ApplesAndOranges == {
    [ tag |-> "Apple", color |-> "red" ],
    [ tag |-> "Orange", seedless |-> TRUE ]
  }
```

We can dynamically reason about the elements of `ApplesAndOranges` based on their tag:

```tla
  \E e \in ApplesAndOranges:
    /\ e.tag = "Apple"
    /\ e.color /= "green"
```

This idiom is quite common in untyped TLA+. [Tagged unions in Paxos][] is
probably the most illuminating example of this idiom. Unfortunately, it is way
too easy to make a typo in the tag name, since it is a string, or simply access
a field, which records marked with the given tag do not have. For example:

```tla
  \E e \in ApplesAndOranges:
    /\ e.tag = "Apple"
    /\ e.seedless
```

**Variants module.** Apalache formalizes the above idiom in the module
[Variants.tla][]. Apalache's type checker alerts users with a type error when
they access a wrong value. Additionally, the default implementation raises an
error in TLC when a variant is used incorrectly.

**Immutability**. All variants are immutable.

**Construction.** An instance of a variant can be constructed via the operator
`Variant`:

```tla
Variant("Apple", "red")
```

If we just construct a variant like in the example above, it will be assigned
a parametric variant type:

```
Apple(Str) | a
```

In this type, we know that whenever a value is tagged with "Apple" it should be
of the string type. However, we know nothing about other options. Most of the
time, we want to define variants that are sealed, that is, we know all
available options. Suppose we wanted to reason about different kinds of fruit, 
but wanted to limit our model to only comparing apples and oranges.
In Apalache, the type for a value that could be either an apple or an orange, but nothing else, 
would be as follows:

```
Apple(Str) | Orange(Bool)
```

To make it easier to represent the fruits, we can introduce variants together with 
user-defined constructors for each option::

```tla
\* @typeAlias: fruit = Apple(Str) | Orange(Bool);

\* @type: Str => $fruit;
Apple(color) == Variant("Apple", color)

\* @type: Bool => $fruit;
Orange(seedless) == Variant("Orange", seedless)
```

Now we can naturally construct apples and orange as follows:

```tla
Apple("red")
Orange(TRUE)
```

Variants can wrap records, for when we want to represent compound data with named fields:

```tla
\* @typeAlias: drink =
\*     Water({ sparkling: Bool })
\*   | Beer({ malt: Str, strength: Int });
\*
\* @type: Bool => $drink;
Water(sparkling) == Variant("Water", [ sparkling |-> sparkling ])

\* @type: (Str, Int) => $drink;
Beer(malt, strength) == Variant("Beer", [ malt |-> malt, strength |-> strength ])
```

Once a variant is constructed, it becomes opaque to the type checker, that is,
the type checker only knows that `Water(TRUE)` and `Beer("Dark", 5)` are both
of type `drink`. This is exactly what we want, in order to combine these values
in a single set. However, we have lost the ability to access the fields of
these values. To deconstruct values of a variant type, we have to use other
operators, presented below.

**Filtering by tag name.** Following the idiomatic use of tagged unions in
untyped TLA+, we can filter a set of variants:

```tla
LET Drinks == { Water(TRUE), Water(FALSE), Beer("Radler", 2) } IN
\E d \in VariantFilter("Beer", Drinks):
    d.strength < 3
```

We believe that `VariantFilter` is the most commonly used way to partition a
set of variants. Note that `VariantFilter` transforms a set of variants into a
set of values (that correspond to the associated tag name).

**Type-safe get.** Sometimes, we do have just a value that does not belong to a
set, so we cannot use `VariantFilter` directly. In this case, we can use
`VariantGetOrElse`:

```tla
LET water == Water(TRUE) IN
VariantGetOrElse("Beer", water,
                 [ malt |-> "Non-alcoholic", strength |-> 0])).strength
```

In the above example, we unpack `water` by using the tag name `"Beer"`.  Since
`water` is actually tagged with `"Water"`, the operator falls back to the
default case and returns the record `[ malt |-> "Non-alcoholic", strength |->
0]`.

**Type-unsafe get.** Sometimes, using `VariantFilter` and `VariantGetOrElse`
is a nuisance, when we know the exact value type. In this case, we can bypass
the type checker and get the value notwithstanding the tag:

```tla
LET drink == ... IN
LET nonFree ==
    IF VariantTag(drink) = "Water"
    THEN VariantGetUnsafe("Water", drink).sparkling
    ELSE VariantGetUnsafe("Beer", drink).strength > 0
IN
...
```

In general, you should avoid using `VariantGetUnsafe`, as it is type unsafe.
Consider the following example:

```tla
  VariantGetUnsafe("Beer", Water(TRUE)).strength
```

In the above example, we treat water as beer. If you try this example with TLC,
it would complain about the missing field `strength`, as it computes some form
of types dynamically. If you try this example with Apalache, it would compute
types statically and in the case of `VariantGetUnsafe` it would simply produce
an arbitrary integer. Most likely, this arbitrary integer would propagate into
an invariant violation and will lead to a spurious counterexample.

----------------------------------------------------------------------------

## Operators

----------------------------------------------------------------------------

<a name="variantCtor"></a>
### Variant constructor

**Notation:** `Variant(tagName, associatedValue)`

**LaTeX notation:** same

**Arguments:** Two arguments: the tag name (a string literal) and a value
(a TLA+ expression).

**Apalache type:** `(Str, a) => tagName(a) | b `, for some types `a` and `b`.
Note that `tagName` is an identifier in this notation. In this type, `b` is a
type variable that captures other options in the variant type.

**Effect:** The variant constructor returns a new value of the variant type.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
\* @typeAlias: drink =
\*     Water({ sparkling: Bool })
\*   | Beer({ malt: Str, strength: Int });
\*
\* @type: Bool => $drink;
Water(sparkling) == Variant("Water", [ sparkling |-> sparkling ])

\* @type: (Str, Int) => $drink;
Beer(malt, strength) == Variant("Beer", [ malt |-> malt, strength |-> strength ])
```

----------------------------------------------------------------------------

<a name="variantTag"></a>
### Variant tag

**Notation:** `VariantTag(variant)`

**LaTeX notation:** same

**Arguments:** One argument: a variant constructed via `Variant`.

**Apalache type:** `(tagName(a) | b) => Str`, for some types `a` and `b`. Note
that `tagName` is an identifier in this notation. In this type, `b` is a type
variable that captures other options in the variant type.

**Effect:** This operator simply returns the tag attached to the variant.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
VariantTag(Variant("Water", [ sparkling |-> sparkling ])) = "Water"
```

----------------------------------------------------------------------------

<a name="variantFilter"></a>
### Variant filter

**Notation:** `VariantFilter(tagName, set)`

**LaTeX notation:** same

**Arguments:** Two arguments: the tag name (a string literal) and a set of
variants (a TLA+ expression).

**Apalache type:** `(Str, Set(tagName(a) | b)) => Set(a)`, for some types `a`
and `b`. Note that `tagName` is an identifier in this notation. In this type,
`b` is a type variable that captures other options in the variant type.

**Effect:** The variant filter keeps the set elements that are tagged with
`tagName`. It removes the tags from these elements and produces the set of
values that were packed with `Variant`.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
\* @typeAlias: drink =
\*     Water({ sparkling: Bool })
\*   | Beer({ malt: Str, strength: Int });
\*
\* @type: Bool => $drink;
Water(sparkling) == Variant("Water", [ sparkling |-> sparkling ])

\* @type: (Str, Int) => $drink;
Beer(malt, strength) == Variant("Beer", [ malt |-> malt, strength |-> strength ])

LET Drinks == { Water(TRUE), Water(FALSE), Beer("Radler", 2) } IN
\E d \in VariantFilter("Beer", Drinks):
    d.strength < 3
```

----------------------------------------------------------------------------

<a name="variantGetOrElse"></a>
### Unpacking a variant safely

**Notation:** `VariantGetOrElse(tagName, variant, defaultValue)`

**LaTeX notation:** same

**Arguments:** Three arguments: the tag name (a string literal), a variant
constructed via `Variant`, a default value compatible with the value carried by
the variant.

**Apalache type:** `(Str, tagName(a) | b, a) => a`, for some types `a` and `b`.
Note that `tagName` is an identifier in this notation. In this type, `b` is a
type variable that captures other options in the variant type.

**Effect:** The operator `VariantGetOrElse` returns the value that was wrapped
via the `Variant` constructor, if the variant is tagged with `tagName`.
Otherwise, the operator returns `defaultValue`.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
\* @typeAlias: drink =
\*     Water({ sparkling: Bool })
\*   | Beer({ malt: Str, strength: Int });
\*
\* @type: Bool => $drink;
Water(sparkling) == Variant("Water", [ sparkling |-> sparkling ])

\* @type: (Str, Int) => $drink;
Beer(malt, strength) == Variant("Beer", [ malt |-> malt, strength |-> strength ])

LET water == Water(TRUE) IN
VariantGetOrElse("Beer", water,
                 [ malt |-> "Non-alcoholic", strength |-> 0])).strength
```

----------------------------------------------------------------------------

<a name="variantGetUnsafe"></a>
### Unpacking a variant unsafely

**Notation:** `VariantGetUnsafe(tagName, variant)`

**LaTeX notation:** same

**Arguments:** Two arguments: the tag name (a string literal) and a variant
constructed via `Variant`.

**Apalache type:** `(Str, tagName(a) | b) => a`, for some types `a` and `b`.
Note that `tagName` is an identifier in this notation. In this type, `b` is a
type variable that captures other options in the variant type.

**Effect:** The operator `VariantGetUnsafe` unconditionally returns some value
that is compatible with the type of values tagged with `tagName`. If `variant`
is tagged with `tagName`, the returned value is the value that was wrapped via
the `Variant` constructor. Otherwise, it is some arbitrary value of a proper type.
As such, this operator does not guarantee that the retrieved value
is always constructed via `Variant`, unless the operator is used with the right tag.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
\* @typeAlias: drink =
\*     Water({ sparkling: Bool })
\*   | Beer({ malt: Str, strength: Int });
\*
\* @type: Bool => $drink;
Water(sparkling) == Variant("Water", [ sparkling |-> sparkling ])

\* @type: (Str, Int) => $drink;
Beer(malt, strength) == Variant("Beer", [ malt |-> malt, strength |-> strength ])

LET drink == Beer("Dunkles", 4) IN
LET nonFree ==
    IF VariantTag(drink) = "Water"
    THEN VariantGetUnsafe("Water", drink).sparkling
    ELSE VariantGetUnsafe("Beer", drink).strength > 0
IN
...
```

[Variants]: https://en.wikipedia.org/wiki/Tagged_union
[Tagged unions in Paxos]: https://github.com/tlaplus/Examples/blob/779852ba9951621f062fc4074b8e81fd12db21dc/specifications/Paxos/Paxos.tla#L85-L106
[Variants.tla]: https://github.com/apalache-mc/apalache/blob/main/src/tla/Variants.tla
