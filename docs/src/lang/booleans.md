# Booleans

[[Back to all operators]](./standard-operators.md)

You find these operators in every programming language and every textbook on
logic. These operators form _propositional logic_.

<a name="const"></a>
## Constants

TLA+ contains three special constants: `TRUE`, `FALSE`, and `BOOLEAN`.
The constant `BOOLEAN` is defined as the set `{FALSE, TRUE}`.

A note for set-theory purists: In theory, `TRUE` and `FALSE` are also sets, but
in practice they are treated as indivisible values. For instance, Apalache and
TLC will report an error, if you try to treat `FALSE` and `TRUE` as sets.

## Operators

**Warning**: Below, we discuss Boolean operators in terms of the way they are usually
defined in programming languages. However, it is important to understand that the
disjunction operator `F \/ G` induces a nondeterministic effect when `F` or `G` contain
the prime operator  (`'`), or when they are used inside the initialization predicate `Init`.
We discuss this effect [Control Flow and Non-determinism].

----------------------------------------------------------------------------

<a name="and"></a>
### And (conjunction)

**Notation:** `F /\ G` or `F \land G`

**LaTeX notation:** ![land](./img/land.png)

**Arguments:** Two or more arbitrary expressions.

**Effect:** The binary case `F /\ G` evaluates to:
    
 - `TRUE`, if both `F` and `G` evaluate to `TRUE`.

 - `FALSE`, if `F` evaluates to `FALSE`,
      or `F` evaluates to `TRUE` and `G` evaluates to `FALSE`.

The general case `F_1 /\ ... /\ F_n` can be understood by evaluating
the expression `F_1 /\ (F_2 /\ ... /\ (F_{n-1} /\ F_n)...)`.

**Determinism:** Deterministic, if the arguments are deterministic.  Otherwise,
the possible effects of non-determinism of each argument are combined.  See
[Control Flow and Non-determinism].

**Errors:** In pure TLA+, the result is undefined if either conjunct evaluates to
a non-Boolean value (the evaluation is lazy).  In this
case, Apalache statically reports a type error, whereas TLC reports a runtime
error.

**Example in TLA+:**

```tla
TRUE  /\ TRUE    \* TRUE
FALSE /\ TRUE    \* FALSE
TRUE  /\ FALSE   \* FALSE
FALSE /\ FALSE   \* FALSE
FALSE /\ 1       \* FALSE in TLC, type error in Apalache
    1 /\ FALSE   \* error in TLC, type error in Apalache
```

**Example in Python:**

```python
True  and True # True
False and True # False
True  and False # False
False and False # False
False and 1 # False, because 1 is cast to True
1 and False # False, because 1 is cast to True

**Special syntax form:** To minimize the number of parentheses, conjunction can
be written in the indented form:

```tla
  /\ F_1
    /\ G_1
    ...
    /\ G_k
  /\ F_2
  ...
  /\ F_n
```

Similar to scopes in Python, the TLA+ parser groups the expressions according
to the number of spaces in front of `/\`. The formula in the above example
is equivalent to:

```tla
  (F_1) /\ ((G_1) /\ ... /\ (G_k)) /\ (F_2) /\ ... /\ (F_n)
```

----------------------------------------------------------------------------

<a name="or"></a>
### Or (disjunction)

**Notation:** `F \/ G` or `F \lor G`

**LaTeX notation:** ![lor](./img/lor.png)

**Arguments:** Two or more Boolean expressions.

**Effect:**

The binary case `F \/ G` evaluates to:
    
 - `FALSE`, if both `F` and `G` evaluate to `FALSE`.

 - `TRUE`, if `F` evaluates to `TRUE`,
      or `F` evaluates to `FALSE` and `G` evaluates to `TRUE`.

The general case `F_1 \/ ... \/ F_n` can be understood by evaluating
the expression `F_1 \/ (F_2 \/ ... \/ (F_{n-1} \/ F_n)...)`.

**Determinism:** deterministic, if the arguments may not update primed
variables.  If the arguments may update primed variables, disjunctions may
result in non-determinism, see [Control Flow and Non-determinism].

**Errors:** In pure TLA+, the result is undefined, if a non-Boolean argument
is involved in the evaluation (the evaluation is lazy).  In this
case, Apalache statically reports a type error, whereas TLC reports a runtime
error.

**Example in TLA+:**

```tla
TRUE  \/ TRUE    \* TRUE
FALSE \/ TRUE    \* TRUE
TRUE  \/ FALSE   \* TRUE
FALSE \/ FALSE   \* FALSE
TRUE  \/ 1       \* TRUE in TLC, type error in Apalache
    1 \/ TRUE    \* error in TLC, type error in Apalache
```

**Example in Python:**

```python
True  or True   # True
False or True   # True
True  or False  # True
False or False  # False
```

**Special syntax form:** To minimize the number of parentheses, disjunction can
be written in the indented form:

```tla
  \/ F_1
    \/ G_1
    ...
    \/ G_k
  \/ F_2
  ...
  \/ F_n
```

Similar to scopes in Python, the TLA+ parser groups the expressions according
to the number of spaces in front of `\/`. The formula in the above example
is equivalent to:

```tla
  (F_1) \/ ((G_1) \/ ... \/ (G_k)) \/ (F_2) \/ ... \/ (F_n)
```

The indented form allows you to combine conjunctions and disjunctions:

```tla
  \/ /\ F
     /\ G
  \/ \/ H
     \/ J
```

The above formula is equivalent to:

```tla
  (F /\ G) \/ (H \/ J)
```

----------------------------------------------------------------------------

<a name="not"></a>
### Negation

**Notation:** `~F` or `\neg F` or `\lnot F`

**LaTeX notation:** ![lnot](./img/lnot.png)

**Arguments:** One argument that should evaluate to a Boolean value.

**Effect:**
 
  The value of `~F` is computed as follows:

  - if `F` is evaluated to `FALSE`, then `~F` is evaluated to `TRUE`,
  - if `F` is evaluated to `TRUE`, then `~F` is evaluated to `FALSE`.

**Determinism:** Deterministic.

**Errors:** In pure TLA+, the result is undefined, if the argument evaluates to
a non-Boolean value. In this case, Apalache statically reports a type error,
whereas TLC reports a runtime error.

**Example in TLA+:**

```tla
~TRUE    \* FALSE
~FALSE   \* TRUE
~(1)     \* error in TLC, type error in Apalache
```

**Example in Python:**

```python
not True    # False
not False   # True
```

----------------------------------------------------------------------------

<a name="implies"></a>
### Implication

**Notation:** `F => G`

**LaTeX notation:** ![implies](./img/implies.png)

**Arguments:** Two arguments. Although they can be arbitrary expressions, the
result is only defined when both arguments are evaluated to Boolean values.

**Effect:** `F => G` evaluates to:

  - `TRUE`, if `F` evaluates to `FALSE`, or
    `F` evaluates to `TRUE` and `G` evaluates to `TRUE`.

  - `FALSE`, if `F` evaluates to `TRUE` and `G` evaluates to `FALSE`.

**Determinism:** Deterministic.

**Errors:** In pure TLA+, the result is undefined, if one of the arguments
evaluates to a non-Boolean value. In this case, Apalache statically reports a
type error, whereas TLC reports a runtime error.

**Example in TLA+:**

```tla
FALSE => TRUE    \* TRUE
TRUE  => TRUE    \* TRUE
FALSE => FALSE   \* TRUE
TRUE  => FALSE   \* FALSE
FALSE => 1       \* TRUE in TLC, type error in Apalache
TRUE  => 1       \* runtime error in TLC, type error in Apalache
1     => TRUE    \* runtime error in TLC, type error in Apalache
```

**Example in Python:**

Recall that `A => B` is equivalent to `~A \/ B`.

```python
(not False) or True     # True
(not True)  or True     # True
(not False) or False    # True
(not True)  or False    # False
```

----------------------------------------------------------------------------

<a name="equiv"></a>
### Equivalence

**Notation:** `F <=> G` or `F \equiv G`

**LaTeX notation:** ![equiv](./img/equiv.png) or ![equiv2](./img/equiv2.png)

**Arguments:** Two arguments. Although they can be arbitrary expressions, the
result is only defined when both arguments are evaluated to Boolean values.

**Effect:** `F <=> G` evaluates to:

  - `TRUE`, if both `F` and `G` evaluate to `TRUE`,
    or both `F` and `G` evaluate to `FALSE`.

  - `FALSE`, if one of the arguments evaluates to `TRUE`,
    while the other argument evaluates to `FALSE`.

How is `F <=> G` different from `F = G`? Actually, `F <=> G` is equality
that is defined only for Boolean values. In other words, if `F` and `G` are
evaluated to Boolean values, then `F <=> G` and `F = G` are evaluated to the
same Boolean value. We prefer `F <=> G` to `F = G`, as `F <=> G` clearly
indicates the intended types of `F` and `G` and thus makes the logical
structure more obvious.

**Determinism:** Deterministic.

**Errors:** In pure TLA+, the result is undefined, if one of the arguments
evaluates to a non-Boolean value. In this case, Apalache statically reports a
type error, whereas TLC reports a runtime error.

**Example in TLA+:**

```tla
FALSE <=> TRUE   \* FALSE
TRUE  <=> TRUE   \* TRUE
FALSE <=> FALSE  \* TRUE
TRUE  <=> FALSE  \* TRUE
FALSE <=> 1      \* runtime error in TLC, type error in Apalache
1     <=> TRUE   \* runtime error in TLC, type error in Apalache
```

**Example in Python:**

Assuming that both expressions are Boolean, `F <=> G` is equivalent to `F = G`.

```python
False == True   # False
True  == True   # True
False == False  # True
True  == False  # False
```

[Control Flow and Non-determinism]: ./control-and-nondeterminism.md
