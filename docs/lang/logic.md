# Logic

[[Back to all operators]](./logic.md)

In this section, you find the operator that, together with [Sets](./sets.md)
form the foundation of TLA+. It is a bit strange that we call this section
"Logic", as the whole language of TLA+ is a logic. However, the operators in
of section can be often see in first-order logic, as opposite to
propositional logic, see [Boooleans](./booleans.md).

Note that the special form `\E y \in S: x' = y` is often used to express
non-determinism in TLA+. See [Control Flow and Non-determinism]. In this
section, we only consider the deterministic version.

----------------------------------------------------------------------------

### Bounded universal quantifier

**Notation:** `\A x \in S: P`

**LaTeX notation:** ![forall-bounded](./img/forall-bounded.png)

**Arguments:** At least three arguments: a variable name, a set, and an
expression. You can also use multiple variables and tuples, see **Advanced
syntax**. As usual in TLA+, if the second argument is not a set, the result is
undefined.

**Effect:** This operator evaluates to a Boolean value. We explain
semantics only for a single variable:

 - `\A x \in S: P` evaluates to `TRUE`, if for every element `e` of `S`, the
   expression `P` evaluates to `TRUE` against the binding `[x |-> e]`.
 - Conversely, `\A x \in S: P` evaluates to `FALSE`, if there exists an element
   `e` of `S` that makes the expression `P` evaluate to `FALSE` against the
   binding `[x |-> e]`.

 _Importantly, when `S = {}`, the expression `\A x \ in S: P` evaluates to
 `TRUE`, independently of what is written in `P`._
   
**Determinism:** Deterministic.

**Errors:** Pure TLA+ does not restrict the operator arguments.  TLC flags a
model checking error, if `S` is infinite.  Apalache produces a static type
error, if the type of elements of `S` is not compatible in the context of `P`
when an element of `S` is bound to `x`.

** Advanced syntax: ** Instead of a single variable `x`, you can use the tuple
syntax to unpack variables from a Cartesian product, see [Tuples](./tuples.md).
For instance, one can write `\A <<x, y>> \in S: P`. In this case, for every
element `e` of `S`, the variable `x` is bound to `e[1]` and `y` is bound to
`e[2]`. The predicate `P` is evaluated against this binding.

Moreover, instead of introducing one variable, one can quantify over several
sets. For instance, you can write: `\A x \in S, y \in T: P`. This form is
simply syntactic sugar for the form with nested quantifiers: `\A x \in S: \A y
\in T: P`.

**Example in TLA+:**

```tla
  \A x \in {1, 2, 3, 4}:
    x > 0
  \* TRUE 
  \A x \in {1, 2, 3, 4}:
    x > 2
  \* FALSE
  \* check the section on tuples to understand the following syntax
  \A <<x, y>> \in { 1, 2 } \X { 3, 4 }:
    x < y
  \* TRUE
```

**Example in Python:** Python conveniently offers us a concise syntax:

```python
  S = frozenset({1, 2, 3, 4})
  all(x > 0 for x in S)         # True
  all(x > 2 for x in S)         # False
  T2 = frozenset((x, y) for x in [1, 2] for y in [3, 4])
  all(x < y for (x, y) in T2)   # True
```

----------------------------------------------------------------------------

### Bounded existential quantifier

**Notation:** `\E x \in S: P`

**LaTeX notation:** ![exists-bounded](./img/exists-bounded.png)

**Arguments:** At least three arguments: a variable name, a set, and an
expression. You can also use multiple variables and tuples, see **Advanced
syntax**. As usual in TLA+, if the second argument is not a set, the result is
undefined.

**Effect:** This operator evaluates to a Boolean value. We explain
semantics only for a single variable:

 - `\E x \in S: P` evaluates to `TRUE`, if there is an element `e` of `S`
    that makes the expression `P` evaluate to `TRUE` against the binding
    `[x |-> e]`.
 - Conversely, `\E x \in S: P` evaluates to `FALSE`, if for all elements
   `e` of `S`, the expression `P` evaluate to `FALSE` against the
   binding `[x |-> e]`.

 _Importantly, when `S = {}`, the expression `\E x \ in S: P` evaluates to
 `FALSE`, independently of what is written in `P`._

 As you probably have noticed, `\E x \in S: P` is equivalent to `~(\A x \in S:
 P)`, and `\A x \in S: P` is equivalent to `~(\E x \in S: P)`. This is called
 _duality_ in logic. But take care!  If `P` contains primes inside, `\E x \in
 S: P` may work as a non-deterministic assignment. In this case, duality does
 not work anymore!  See [Control Flow and Non-determinism].
   
**Determinism:** Deterministic, unless `P` contains primes.
For the non-deterministic case, see [Control Flow and Non-determinism].

**Errors:** Pure TLA+ does not restrict the operator arguments.  TLC flags a
model checking error, if `S` is infinite.  Apalache produces a static type
error, if the type of elements of `S` is not compatible in the context of `P`
when an element of `S` is bound to `x`.

**Advanced syntax:** Instead of a single variable `x`, you can use the tuple
syntax to unpack variables from a Cartesian product, see [Tuples](./tuples.md).
For instance, one can write `\E <<x, y>> \in S: P`. In this case, for every
element `e` of `S`, the variable `x` is bound to `e[1]` and `y` is bound to
`e[2]`. The predicate `P` is evaluated against this binding.

Moreover, instead of introducing one variable, one can quantify over several
sets. For instance, you can write: `\E x \in S, y \in T: P`. This form is
simply syntactic sugar for the form with nested quantifiers: `\E x \in S: \E y
\in T: P`.

**Example in TLA+:**

```tla
  \E x \in {1, 2, 3, 4}:
    x > 0
  \* TRUE 
  \E x \in {1, 2, 3, 4}:
    x > 2
  \* TRUE
  \* check the section on tuples to understand the following syntax
  \E <<x, y>> \in { 1, 2 } \X { 3, 4 }:
    x < y
  \* TRUE
```

**Example in Python:** Python conveniently offers us a concise syntax:

```python
  S = frozenset({1, 2, 3, 4})
  some(x > 0 for x in S)        # True
  some(x > 2 for x in S)        # False
  T2 = frozenset((x, y) for x in [1, 2] for y in [3, 4])
  some(x < y for (x, y) in T2)  # True
```

----------------------------------------------------------------------------

### Unbounded universal quantifier

**Notation:** `\A x: P`

**LaTeX notation:** ![forall](./img/forall.png)

**Arguments:** At least two arguments: a variable name and an
expression. 

**Effect:** This operator evaluates to a Boolean value. It evaluates to `TRUE`,
when every element in the logical universe makes the expression `P` evaluate to
`TRUE` against the binding `[x |-> e]`. More precisely, we have to consider
only the elements that produced a defined result when evaluating `P`.

Neither TLC, nor Apalache support this operator. It is impossible to give
operational semantics for this operator, unless we explicitly introduce the
universe. It requires a first-order logic solver. This operator may be useful
when writing proofs with [TLAPS].

----------------------------------------------------------------------------

### Unbounded existential quantifier

**Notation:** `\E x: P`

**LaTeX notation:** ![exists](./img/exists.png)

**Arguments:** At least two arguments: a variable name and an
expression. 

**Effect:** This operator evaluates to a Boolean value. It evaluates to `TRUE`,
when at least one element in the logical universe makes the expression `P`
evaluate to `TRUE` against the binding `[x |-> e]`. More precisely, we have to
consider only the elements that produced a defined result when evaluating `P`.

Neither TLC, nor Apalache support this operator. It is impossible to give
operational semantics for this operator, unless we explicitly introduce the
universe. It requires a first-order logic solver. This operator may be useful
when writing proofs with [TLAPS].


[Control Flow and Non-determinism]: ./control-and-nondeterminism.md
[TLAPS]: https://tla.msr-inria.inria.fr/tlaps/content/Home.html

