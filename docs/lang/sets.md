# Sets

[[Back to all operators]](./standard-operators.md)

Sets are the foundational data structure in TLA+. (Similar to what lists are in
Lisp and Python). The other TLA+ data structures can be all expressed with
sets: functions, records, tuples, sequences. So it is important to understand
TLA+ sets well. In contrast to programming languages, there is no efficiency
penalty in using sets instead of sequences: TLA+ does not have a compiler, the
efficiency is measured in time it takes the human brain to understand the
specification.

Basic properties of sets...

Sets are immutable.

Sets are similar to `frozenset` in Python and immutable `Set` in `Java`.
But we don't need hashes, only equality.

Comparable values in a set. See Section 14.7.2 of [Specifying Systems].

----------------------------------------------------------------------------

## Operators

### Set constructor

**Notation:** `{e_1, ..., e_n}`

**LaTeX notation:** `{e_1, ..., e_n}`

**Arguments:** Any number of arguments, `n >= 0`.

**Effect:** Produce the set that contains the values of the expressions `e_1,
..., e_n`, in no particular order, and only these values. If `n = 0`, the
empty set is constructed.

**Determinism:** Deterministic.

**Errors:** Pure TLA+ does not restrict the set elements. They can be any
combination of TLA+ values: Booleans, integers, strings, sets, functions, etc.

TLC only allows to construct sets out of the elements that are comparable. For
instance, two integers are comparable, but an integer and a set are not
comparable. See Section 14.7.2 of [Specifying Systems].

Apalache goes further and requires the set elements to have the same type.
If this is not the case, the type checker flags an error.

**Example in TLA+:**

```tla
  { 1, 2, 3 }               \* a flat set of integers
  { { 1, 2 }, { 2, 3 } }    \* a set of sets of integers
  { FALSE, 1 }              \* a set of mixed elements.
                            \* Model checking error in TLC, type error in Apalache
```

**Example in Python:** TLA+ sets are immutable, so we are using `frozenset`:

```python
  frozenset([1, 2, 3])
  frozenset([frozenset([1, 2]), frozenset([2, 3])])
  frozenset([False, 1])
```

----------------------------------------------------------------------------

### Set membership

**Notation:** `e \in S`

**LaTeX notation:** ![in](./img/in-set.png)

**Arguments:** Two arguments.  If the second argument is not a set, the result
is undefined.

**Effect:** This operator evaluates to:

  - `TRUE`, if `S` is a set that contains an element that is equal to the value
    of `e`; and
  - `FALSE`, if `S` is a set and all of its elements are not equal to the
    value of `e`.
    
**Warning:** If you are using the special form `x' \in S`, this operator may
assign a value to `x'` as a side effect. See [Control Flow and Non-determinism].

**Determinism:** Deterministic, unless you are using the special form `x' \in
S` to assign a value to `x'`, see [Control Flow and Non-determinism].

**Errors:** Pure TLA+ does not restrict the operator arguments.  TLC flags a
model checking error, when it discovers that `e` cannot be compared to the
elements of `S`. Apalache produces a static type error, if the type of `e` is
incompatible with the type of elements of `S`, or if `S` is not a set.

**Example in TLA+:**

```tla
  1 \in { 1, 2, 3 }         \* TRUE
  10 \in { 1, 2, 3 }        \* FALSE
  {} \in { {1}, {2} }       \* FALSE
  1 \in { "a", "b" }        \* model checking error in TLC,
                            \* static type error in Apalache
```

**Example in Python:** Python conveniently offers us `in`:

```python
  1 in frozenset([1, 2, 3])     # True
  10 in frozenset([1, 2, 3])    # False
  1 in frozenset(["a", "b"])    # False
```

----------------------------------------------------------------------------

### Set non-membership

**Notation:** `e \notin S`

**LaTeX notation:** ![notin](./img/notin-set.png)

**Arguments:** Two arguments.  If the second argument is not a set, the result
is undefined.

**Effect:** This operator evaluates to:

  - `FALSE`, if `S` is a set that contains an element that is equal to the value
    of `e`; and
  - `TRUE`, if `S` is a set and all of its elements are not equal to the
    value of `e`.

**Determinism:** Deterministic.

**Errors:** Pure TLA+ does not restrict the operator arguments.  TLC flags a
model checking error, when it discovers that `e` cannot be compared to the
elements of `S`. Apalache produces a static type error, if the type of `e` is
incompatible with the type of elements of `S`, or if `S` is not a set.

**Example in TLA+:**

```tla
  1 \notin { 1, 2, 3 }      \* FALSE
  10 \notin { 1, 2, 3 }     \* TRUE
  {} \notin { {1}, {2} }    \* TRUE
  1 \notin { "a", "b" }     \* model checking error in TLC,
                            \* static type error in Apalache
```

**Example in Python:** Python conveniently offers us `not in`:

```python
  1 not in frozenset([1, 2, 3])     # False
  10 not in frozenset([1, 2, 3])    # True
  1 not in frozenset(["a", "b"])    # True
```

----------------------------------------------------------------------------

### Equality and inequality

The operators `a = b` and `a /= b` are core operators of TLA+,
see [Logic](./logic.md).

----------------------------------------------------------------------------

### Set inclusion

**Notation:** `S \subseteq T`

**LaTeX notation:** ![subseteq](./img/subseteq.png)

**Arguments:** Two arguments.  If both arguments are not sets, the result
is undefined.

**Effect:** This operator evaluates to:

  - `TRUE`, if `S` and `T` are sets, and every element of `S` is a member of `T`;
  - `FALSE`, if `S` and `T` are sets, and there is an element of `T` that
    is not a member of `S`.

**Determinism:** Deterministic.

**Errors:** Pure TLA+ does not restrict the operator arguments.  TLC flags a
model checking error, when it discovers that elements of `S` cannot be compared
to the elements of `T`. Apalache produces a static type error, `S` and `T` are
either not sets, or sets of incompatible types.

**Example in TLA+:**

```tla
  { 1, 2 }    \subseteq { 1, 2, 3 }     \* TRUE
  { 1, 2, 3 } \subseteq { 1, 2, 3 }     \* TRUE
  { 1, 2, 3 } \subseteq { 1, 2 }        \* FALSE
  { {1} }     \subseteq { 1, 2, 3 }     \* FALSE, model checking error in TLC
                                        \* static type error in Apalache
```

**Example in Python:** Python conveniently offers us `<=`:

```python
  frozenset([1, 2]) <= frozenset([1, 2, 3])             # True
  frozenset([1, 2, 3]) <= frozenset([1, 2, 3])          # True
  frozenset([1, 2, 3]) <= frozenset([1, 2])             # False
  frozenset([frozenset([1])]) <= frozenset([1, 2, 3])   # False
```

----------------------------------------------------------------------------

### Proper set inclusion

**Notation:** `S \subset T`

**LaTeX notation:** ![subset](./img/subset.png)

**Arguments:** Two arguments.  If both arguments are not sets, the result
is undefined.

**Effect:** This operator evaluates to:

  - `TRUE`, if `S \subseteq T /\ S /= T` evaluates to `TRUE`;
  - `FALSE`, if `S` and `T` are sets, and `~(S \subseteq T) \/ S = T` evaluates
    to `TRUE`.

**Determinism:** Deterministic.

**Errors:** Pure TLA+ does not restrict the operator arguments.  TLC flags a
model checking error, when it discovers that elements of `S` cannot be compared
to the elements of `T`. Apalache produces a static type error, `S` and `T` are
either not sets, or sets of incompatible types.

**Example in TLA+:**

```tla
  { 1, 2 }    \subset { 1, 2, 3 }     \* TRUE
  { 1, 2, 3 } \subset { 1, 2, 3 }     \* FALSE
  { 1, 2, 3 } \subset { 1, 2 }        \* FALSE
  { {1} }     \subset { 1, 2, 3 }     \* FALSE, model checking error in TLC
                                      \* static type error in Apalache
```

**Example in Python:** Python conveniently offers us `<`:

```python
  frozenset([1, 2]) < frozenset([1, 2, 3])             # True
  frozenset([1, 2, 3]) < frozenset([1, 2, 3])          # False
  frozenset([1, 2, 3]) < frozenset([1, 2])             # False
  frozenset([frozenset([1])]) < frozenset([1, 2, 3])   # False
```

----------------------------------------------------------------------------

### Set containment

**Notation:** `S \supseteq T`

**LaTeX notation:** ![supseteq](./img/supseteq.png)

**Arguments:** Two arguments.  If both arguments are not sets, the result
is undefined.

**Effect:** This operator evaluates to:

  - `TRUE`, if `S` and `T` are sets, and every element of `T` is a member of `S`;
  - `FALSE`, if `S` and `T` are sets, and there is an element of `S` that
    is not a member of `T`.

  It is easy to see, that `S \supseteq T` if and only if `T \subseteq S`.

**Determinism:** Deterministic.

**Errors:** Pure TLA+ does not restrict the operator arguments.  TLC flags a
model checking error, when it discovers that elements of `S` cannot be compared
to the elements of `T`. Apalache produces a static type error, `S` and `T` are
either not sets, or sets of incompatible types.

**Example in TLA+:**

```tla
  { 1, 2 }    \supseteq { 1, 2, 3 }     \* FALSE
  { 1, 2, 3 } \supseteq { 1, 2, 3 }     \* TRUE
  { 1, 2, 3 } \supseteq { 1, 2 }        \* TRUE
  { {1} }     \supseteq { 1, 2, 3 }     \* FALSE, model checking error in TLC
                                        \* static type error in Apalache
```

**Example in Python:** Python conveniently offers us `>=`:

```python
  frozenset([1, 2]) >= frozenset([1, 2, 3])             # False
  frozenset([1, 2, 3]) >= frozenset([1, 2, 3])          # True
  frozenset([1, 2, 3]) >= frozenset([1, 2])             # True
  frozenset([frozenset([1])]) >= frozenset([1, 2, 3])   # False
```

----------------------------------------------------------------------------

### Proper set containment

**Notation:** `S \supset T`

**LaTeX notation:** ![supset](./img/supset.png)

**Arguments:** Two arguments.  If both arguments are not sets, the result
is undefined.

**Effect:** This operator evaluates to:

  - `TRUE`, if `S \supseteq T /\ S /= T` evaluates to `TRUE`;
  - `FALSE`, if `S` and `T` are sets, and `~(S \supseteq T) \/ S = T` evaluates
    to `TRUE`.

**Determinism:** Deterministic.

**Errors:** Pure TLA+ does not restrict the operator arguments.  TLC flags a
model checking error, when it discovers that elements of `S` cannot be compared
to the elements of `T`. Apalache produces a static type error, `S` and `T` are
either not sets, or sets of incompatible types.

**Example in TLA+:**

```tla
  { 1, 2 }    \supset { 1, 2, 3 }       \* FALSE
  { 1, 2, 3 } \supset { 1, 2, 3 }       \* FALSE
  { 1, 2, 3 } \supset { 1, 2 }          \* TRUE
  { {1} }     \supseteq { 1, 2, 3 }     \* FALSE, model checking error in TLC
                                        \* static type error in Apalache
```

**Example in Python:** Python conveniently offers us `>`:

```python
  frozenset([1, 2]) > frozenset([1, 2, 3])              # False
  frozenset([1, 2, 3]) > frozenset([1, 2, 3])           # False
  frozenset([1, 2, 3]) > frozenset([1, 2])              # True
  frozenset([frozenset([1])]) >= frozenset([1, 2, 3])   # False
```




[Control Flow and Non-determinism]: ./control-and-nondeterminism.md
[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=learning.html#book

