# Integers

[[Back to all operators]](./standard-operators.md)

The integer literals are the part of the core language. The are written by
using the standard syntax: 0, 1, -1, 2, -2, 3, -3, ... Importantly, TLA+
integers are unbounded. They do not have any fixed bit width, and they cannot
overflow.

The integer operators are defined in the standard module `Integers`. To use
it, write the `EXTENDS` clause in the first lines of your module. Like this:

```tla
---- MODULE MyArithmetics ----
EXTENDS Integers
...
==============================
```

## Constants

The module `Integers` defines two constant sets:

 - The set `Int` that consists of all integers. _This set is infinite._
 - The set `Nat` that consists of all natural numbers, that is,
   `Nat` contains every integer `x` that has the property `x >= 0`.
   _This set is infinite._

----------------------------------------------------------------------------

## Operators

### Integer range

**Notation:** `a..b`

**LaTeX notation:** `a..b`

**Arguments:** Two arguments. The result is only defined when both arguments
are evaluated to integer values.

**Effect:** `a..b` evaluates to the set `{i \in Int: a <= i /\ i <= b}`, that
is, the set of all integers in the range from `a` to `b`, including `a` and `b`.
If `a > b`, then `a..b` is the empty set `{}`.

**Determinism:** Deterministic.

**Errors:** In pure TLA+, the result is undefined, if one of the arguments
evaluates to a non-integer value. In this case, Apalache statically reports a
type error, whereas TLC reports a runtime error.

**Example in TLA+:**

```tla
  0..10    \* { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 }
  -5..3    \* { -5, -4, -3, -2, -1, 0, 1, 2, 3 }
  10..0    \* { }
  "a".."z" \* runtime error in TLC, type error in Apalache
  {1}..{3} \* runtime error in TLC, type error in Apalache
```

**Example in Python:** `a..b` can be written as `set(range(a, b + 1))` in
python.

```python
  set(range(0, 10))   # {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
  set(range(10, 0))   # set()
```

 - Integer algebra: `-i`, `i + k`, `i - k`, `i * k`, `i^k`, `i \div k`, `i % k`

----------------------------------------------------------------------------

### Unary integer negation

**Notation:** `-i`

**LaTeX notation:** `-i`

**Arguments:** One argument. The result is only defined when the argument
evaluates to an integer.

**Effect:** `-i` evaluates to the negation of `i`.

**Determinism:** Deterministic.

**Errors:** In pure TLA+, the result is undefined, if the argument
evaluates to a non-integer value. In this case, Apalache statically reports a
type error, whereas TLC reports a runtime error.

**Example in TLA+:**

```tla
  -(5)    \* -5, note that '-5' is just a literal, not operator application
  -(-5)   \* 5
  -x      \* negated value of x
```

**Example in Python:** 

```python
  -(5)
  -(-5)
```

----------------------------------------------------------------------------

### Integer addition

**Notation:** `a + b`

**LaTeX notation:** `a + b`

**Arguments:** Two arguments. The result is only defined when both arguments
are evaluated to integer values.

**Effect:** `a + b` evaluates to the sum of `a` and `b`.

**Determinism:** Deterministic.

**Errors:** No overflow is possible. In pure TLA+, the result is undefined, if
one of the arguments evaluates to a non-integer value. In this case, Apalache
statically reports a type error, whereas TLC reports a runtime error.

**Example in TLA+:**

```tla
  5 + 3     \* 8
  (-5) + 3  \* -2
```

**Example in Python:** 

```python
  5 + 3
  (-5) + 3
```

----------------------------------------------------------------------------

### Integer subtraction

**Notation:** `a - b`

**LaTeX notation:** `a - b`

**Arguments:** Two arguments. The result is only defined when both arguments
are evaluated to integer values.

**Effect:** `a - b` evaluates to the difference of `a` and `b`.

**Determinism:** Deterministic.

**Errors:** No overflow is possible. In pure TLA+, the result is undefined, if
one of the arguments evaluates to a non-integer value. In this case, Apalache
statically reports a type error, whereas TLC reports a runtime error.

**Example in TLA+:**

```tla
  5 - 3         \* 2
  (-5) - 3      \* -8
  (-5) - (-3)   \* -2
```

**Example in Python:** 

```python
  5 - 3
  (-5) - 3
  (-5) - (-3)
```

----------------------------------------------------------------------------

### Integer multiplication

**Notation:** `a * b`

**LaTeX notation:** `a * b`

**Arguments:** Two arguments. The result is only defined when both arguments
are evaluated to integer values.

**Effect:** `a * b` evaluates to the product of `a` and `b`.

**Determinism:** Deterministic.

**Errors:** No overflow is possible. In pure TLA+, the result is undefined, if
one of the arguments evaluates to a non-integer value. In this case, Apalache
statically reports a type error, whereas TLC reports a runtime error.

**Example in TLA+:**

```tla
  5 * 3     \* 15
  (-5) * 3  \* -15
```

**Example in Python:** 

```python
  5 * 3
  (-5) * 3
```

----------------------------------------------------------------------------

### Integer division

**Notation:** `a \div b`

**LaTeX notation:** ![div](./img/div.png)

**Arguments:** Two arguments. The result is only defined when both arguments
are evaluated to integer values, and the second argument is different from 0.

**Effect:** `a \div b` is defined as follows:

 - when `a >= 0` and `b > 0`, then the result of `a \div b` is
    the integer `c` that has the property: `a = b * c + d`
    for some `d` in `0..(b-1)`.
 - when `a >= 0` and `b < 0`, then the result of `a \div b` is
    the integer `c` that has the property: `a = b * c + d`
    for some `d` in `0..(-b-1)`.
 - when `a < 0` and `b < 0`, then the result of `a \div b` is
    the integer `c` that has the property: `a = b * c + d`
    for some `d` in `0..(-b-1)`.
 - when `a < 0` and `b > 0`, then the result of `a \div b` is
    the integer `c` that has the property: `a = b * c + d`
    for some `d` in `0..(b-1)`.

**Determinism:** Deterministic.

**Errors:** No overflow is possible. In pure TLA+, the result is undefined, if
one of the arguments evaluates to a non-integer value. In this case, Apalache
statically reports a type error, whereas TLC reports a runtime error. The value
of `a \div b` is undefined for `b = 0`.

**Example in TLA+:** Here are the examples for the four combinations of signs:

```tla
   100 \div 3       \*  33
  -100 \div (-3)    \*  34
   100 \div (-3)    \* -33       
  -100 \div 3       \* -34       
```

**Example in Python:** Here are the examples for the four combinations of signs
to produce the same results as in TLA+:

```python
  int(100 / 3)          #  33
  int(-100 / (-3)) + 1  #  34
  int(100 / (-3))       # -33
  int(-100 / 3) - 1     # -34
```

----------------------------------------------------------------------------

### Integer remainder

**Notation:** `a % b`

**LaTeX notation:** `a % b`

**Arguments:** Two arguments. The result is only defined when both arguments
are evaluated to integer values, and the second argument is different from 0.

**Effect:** `a % b` is the number `c` that has the property:
`a = b * (a \div b) + c`.

**Determinism:** Deterministic.

**Errors:** No overflow is possible. In pure TLA+, the result is undefined, if
one of the arguments evaluates to a non-integer value. In this case, Apalache
statically reports a type error, whereas TLC reports a runtime error. The value
of `a % b` is undefined for `b = 0`.

**Example in TLA+:** Here are the examples for the four combinations of signs:

```tla
  100  % 3      \* 1
  -100 % (-3)   \* 2
  100  % (-3)   \* 1
  -100 % 3      \* 2
```

**Example in Python:** Here are the examples for the four combinations of signs
to produce the same results as in TLA+:

```python
  100 % 3          # 1
  -100 % (-3) + 3  # 2
  100 % (-3) + 3   # 1
  -100 % 3         # 2
```

