# Option Types

[[Back to Apalache extensions]](./apalache-extensions.md)

[Option types](https://en.wikipedia.org/wiki/Option_type) are useful when you
want to internalize reasoning about partial functions. A simple motivating
example is division over integers, for which `n/0` is undefined.

The basic idea is as follows: given a partial function `f : A -> B`, we form the
type `Option(B)` by extending `B` with an element representing a missing value,
`None`, and lift each value `b` in `B` to `Some(b)`, allowing us to represent
the partial function `pf : A -> Option(B)`, such that, for each `a` in `A`,
`pf(a) = Some(f(a))` iff `f(a)` is defined, and `None` otherwise.


Apalache leverages its support for [variants](./variants.md) to define a
polymorphic option type along with some common utility functions in the module
[Option.tla][]. 

The module defines a type alias `$option` as

```tla
\* @typeAlias: option = Some(a) | None(UNIT);
```

However, due to the current lack of support for polymorphic aliases, this alias
has limited utility, and parametric option types can only be properly expressed
by writing out the full variant type `Some(a) | None(UNIT)`.
Nonetheless, in this manual page, we will sometimes write `$option(a)`
as a shorthand for the type `Some(a) | None(UNIT)`.

In the context of TLA+, our encoding of option types is generalized over
"partial operators", meaning operators which return a value of type
`$option(a)`. Support for partial functions is supplied by two operators,
[OptionPartialFun](#OptionPartialFun) and [OptionFunApp](#OptionFunApp).

## Operators

### Constructing present optional values

**Notation:** `Some(v)`

**LaTeX notation:** same

**Apalache type:** `(a) => Some(a) | None(UNIT)`, for some type `a`.

**Arguments:** The value `v` of type `a` to be lifted into the
option.

**Effect:** Produces a new value of the optional type.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
\* @type: Some(Int) | None(UNIT);
SomeInt == Some(42)
```

### Constructing absent optional values

**Notation:** `None`

**LaTeX notation:** same

**Apalache type:** `Some(a) | None(UNIT)`, for some type `a`.

**Arguments:** None

**Effect:** Produces a representation of an absent value.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
\* @type: Some(Int) | None(UNIT);
NoInt == None
```
----------------------------------------------------------------------------

### Checking for presence or absence of a value

**Notation:** `IsSome(o)` or `IsNone(o)`

**LaTeX notation:** same

**Apalache type:** `(Some(a) | None(UNIT)) => Bool`, for some type `a`.

**Arguments:** One argument: a value of type `$option(a)` for some type `a`.

**Effect:** These operators are `TRUE` or `FALSE` depending on whether the
optional value is present or absent, in the expected way.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
TRUE = IsSome(Some(5)) /\ IsNone(None)
```

----------------------------------------------------------------------------

### Case analysis and elimination of optional values

**Notation:** `OptionCase(o, caseSome, caseNone)`

**LaTeX notation:** same

**Apalache type:** `(Some(a) | None(UNIT), a => b, UNIT => b) => b`,
for some types `a` and `b`. 

**Arguments:**

- `o` an optional value
- `caseSome` is an operator to be applied to a present value
- `caseNone` is an operator to be applied to the `UNIT` if the value is absent

**Effect:** `OptionCase(o, caseSome, caseNone)` is `caseSome(v)` if `o =
Some(v)`, or else `caseNone(UNIT)`. This is a way of eliminating a value of type
`Option(a)` to produce a value of type `b`.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
/\ LET
    \* @type: Int => Int;
    caseSome(x) == x + 1
    IN LET
    \* @type: UNIT => Int;
    caseNone(u) == 0
    IN
    OptionCase(Some(3), caseSome, caseNone) = 4
/\ LET
    \* @type: Int => Str;
    caseSome(x) == "Some Number"
    IN LET
    \* @type: UNIT => Str;
    caseNone(u) == "None"
    IN
    OptionCase(None, caseSome, caseNone) = "None"
```

----------------------------------------------------------------------------

### Sequencing application of partial operators

**Notation:** `OptionFlatMap(f, o)`

**LaTeX notation:** same

**Apalache type:**
`(a => Some(b) | None(UNIT), Some(a) | None(UNIT)) => Some(b) | None(UNIT)`,
for some types `a` and `b`. 

**Arguments:**

- `f` is a partial operator
- `o` an optional value

**Effect:** `OptionFlatMap(f, o)` is `f(v)` if `o = Some(v)`, or else `None`.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
LET incr(n) == Some(n + 1) IN
LET fail(n) == None IN
LET q == OptionFlatMap(incr, Some(1)) IN
LET r == OptionFlatMap(incr, q) IN
LET s == OptionFlatMap(fail, r) IN
/\ r = Some(3)
/\ s = None
```

----------------------------------------------------------------------------

### Unwrapping optional values

**Notation:** `OptionGetOrElse(o, default)`

**LaTeX notation:** same

**Apalache type:** `(Some(a) | None(UNIT), a) => a`, for some type `a`.

**Arguments:**

- `o` an optional value
- `default` is a default value to return

**Effect:**
`OptionGetOrElse(o, default)` is `v` iff `o = Some(v)`, or else `default`.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
\* @type: Set(Int) => Some(Int) | None(UNIT);
MaxSet(s) ==
  LET max(oa, b) ==
    IF OptionGetOrElse(oa, b) > b
    THEN oa
    ELSE Some(b)
  IN
  ApaFoldSet(max, None, s)
```

----------------------------------------------------------------------------

### Converting optional values

#### Converting to sequences

**Notation:** `OptionToSeq(o)`

**LaTeX notation:** same

**Apalache type:** `(Some(a) | None(UNIT)) => Seq(a)`, for some type `a`.

**Arguments:**

- `o` an optional value

**Effect:** `OptionToSeq(o)` is `<<v>>` iff `o = Some(v)`, or else `<<>>`.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
LET \* @type: Seq(Int);
    empty == <<>>
IN
/\ OptionToSeq(None) = empty
/\ OptionToSeq(Some(1)) = <<1>>
```

#### Converting to sets

**Notation:** `OptionToSet(o)`

**LaTeX notation:** same

**Apalache type:** `(Some(a) | None(UNIT)) => Seq(a)`, for some type `a`.

**Arguments:**

- `o` an optional value

**Effect:** `OptionToSet(o)` is like `OptionToSeq`, but producing a set.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
LET \* @type: Set(Int);
    empty == {}
IN
/\ OptionToSet(None) = empty
/\ OptionToSet(Some(1)) = {1}
```

----------------------------------------------------------------------------

### Obtaining an optional value from a set

**Notation:** `OptionGuess(s)`

**LaTeX notation:** same

**Apalache type:** `Set(a) => Some(a) | None(UNIT)`, for some type `a`.

**Arguments:**

- `s` is a set

**Effect:** `OptionGuess(s)` is `None` if `s = {}`, otherwise it is `Some(x)`,
where `x \in s`. `x` is selected from `s` nondeterministically.

**Determinism:** Nondeterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
LET
    \* @type: Set(Int);
    empty == {}
IN
/\ OptionGuess(empty) = None
/\ LET choices == {1,2,3,4} IN
    LET choice == OptionGuess(choices) IN
    VariantGetUnsafe("Some", choice) \in choices
```

----------------------------------------------------------------------------

<a name="OptionFunApp"></a>
### Apply a function to a partial value

**Notation:** `OptionFunApp(f, o)`

**LaTeX notation:** same

**Apalache type:** `(a -> b, Some(a) | None(UNIT)) => Some(b) | None(UNIT)`

**Arguments:**

- `f` is a function
- `o` is an optional value

**Effect:**
`OptionFunApp(f, o)` is `Some(f[v])` if `o = Some(v)` or else `None`.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
LET f == [x \in 1..3 |-> x + 1] IN
/\ OptionFunApp(f, Some(1)) = Some(2)
/\ OptionFunApp(f, None) = None
```

----------------------------------------------------------------------------

<a name="OptionPartialFun"></a>
### Extend a total function into a partial function

**Notation:** `OptionPartialFun(f, undef)`

**LaTeX notation:** same

**Apalache type:** `(a -> b, Set(a)) => (a -> Some(b) | None(UNIT))`

**Arguments:**

- `f` is a total function
- `undef` is a set of values for which the new function is to be "undefined"

**Effect:** `OptionPartialFun(f, undef)` is a function mapping each value in
`undef` to `None`, and each value `x \in (DOMAIN f \ undef)` to `Some(f[x])`.
This can be used to extend a total function into a "partial function"
whose domain is extended to include the values in 'undef'.

**Determinism:** Deterministic.

**Errors:** No errors.

**Example in TLA+:**

```tla
LET def == 1..3 IN
LET undef == 4..10 IN
LET f == [x \in def |-> x + 1] IN
LET pf == OptionPartialFun(f, undef) IN
/\ \A n \in def: pf[n] = Some(n + 1)
/\ \A n \in undef: pf[n] = None
```

[Option.tla]: https://github.com/informalsystems/apalache/blob/main/src/tla/Option.tla
