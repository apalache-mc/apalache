# Apalache operators

In addition to the standard TLA+ operators described in the previous section, Apalache defines a number of operators, which do not belong to the core language of TLA+, but which Apalache uses to provide clarity, efficiency, or special functionality. These operators belong to the module `Apalache`, and can be used in any specification by declaring `EXTENDS Apalache`.

<a name="Assignment"></a>
## Assignment

**Notation:** `v' := e`

**LaTeX notation:** ![coloneq](./img/coloneq.png)

**Arguments:** Two arguments. The first is a primed variable name, the second is arbitrary.

**Apalache type:** `(a, a) => Bool`, for some type `a`

**Effect:** The expression `v' := e` evaluates to `v' = e`. At the level of Apalache static analysis, such expressions indicate parts of an action, where the value of a state-variable in a successor state is determined. See [here](../idiomatic/001assignments.md) for more details about assignments in Apalache.

**Determinism:** Deterministic.

**Errors:** 
If the first argument is not a primed variable name, or if the assignment operator is used where assignments are prohibited, Apalache statically reports an error.

**Example in TLA+:**

```tla
x' := 1                   \* x' = 1 
x' := (y = z)             \* x' = (y = z) 
x' := (y' := z)           \* x' = (y' = z) in TLC, assignment error in Apalache 
x' := 1 \/ x' := 2        \* x' = 1 \/ x' = 2 
x' := 1 /\ x' := 2        \* FALSE in TLC, assignment error in Apalache
x' := 1 \/ x' := "a"      \* Type error in Apalache 
(x' + 1) := 1             \* (x' + 1) = 1 in TLC, assignment error in Apalache 
IF x' := 1 THEN 1 ELSE 0  \* Assignment error in Apalache
```

**Example in Python:**

```python
>> a = 1          # a' := 1
>> a == 1         # a' = 1
True
>> a = b = "c"    # b' := "c" /\ a' := b'
>> a = (b == "c") # a' := (b = "c")
```

----------------------------------------------------------------------------

<a name="Gen"></a>
## Value generators

**Notation:** `Gen(bound)`

**LaTeX notation:** `Gen(bound)`

**Arguments:** One argument: an integer literal or a constant expression (of
the integer type).

**Apalache type:** `Int => a`, for some type `a`.

**Effect:** A generator of a data structure. Given a positive integer `bound`,
and assuming that the type of the operator application is known, we recursively
generate a TLA+ data structure as a tree, whose width is bound by the number
`bound`.

**Determinism:** The generated data structure is unrestricted.  It is
effectively implementing data non-determinism.

**Errors:**
If the type of `Gen` cannot be inferred from its application context,
or if `bound` is not an integer, Apalache reports an error.

**Example in TLA+:**

```tla
\* produce an unrestricted integer
LET \* @type: Int;
    oneInt == Gen(1)
IN
\* produce a set of integers up to 10 elements
LET \* @type: Set(Int);
    setOfInts == Gen(10)
IN
\* produce a sequence of up to 10 elements
\* that are integers up to 10 elements each
LET \* @type: Seq(Set(Int));
    sequenceOfInts == Gen(10)
IN
...
```

----------------------------------------------------------------------------

## Folding

The operators `FoldSet` and `FoldSeq` are explained in more detail in a dedicated section [here](../apalache/fold.md).

----------------------------------------------------------------------------

<a name="SetAsFun"></a>

## Convert a set of pairs to a function

**Notation:** `SetAsFun(S)`

**LaTeX notation:** `SetAsFun(S)`

**Arguments:** One argument: A set of pairs `S`, which may be empty.

**Apalache type:** `Set(<<a, b>>) => (a -> b)`, for some types `a` and `b`.

**Effect:** Convert a set of pairs `S` to a function `F`, with the property that `F(x) = y => <<x,y>> \in S`. Note that if `S`
contains at least two pairs `<<x, y>>` and `<<x, z>>`, such that `y /= z`, then `F` is not uniquely defined.
We use `CHOOSE` to resolve this ambiguity. The operator `SetAsFun` can be defined as follows:

```tla
SetAsFun(S) ==
    LET Dom == { x: <<x, y>> \in S }
        Rng == { y: <<x, y>> \in S }
    IN
    [ x \in Dom |-> CHOOSE y \in Rng: <<x, y>> \in S ]
```

Apalache implements a more efficient encoding of this operator than the default one.

**Determinism:** Deterministic.

**Errors:**
If `S` is ill-typed, Apalache reports an error.

**Example in TLA+:**

```tla
SetAsFun({ <<1, 2>>, <<3, 4>> }) = [x \in { 1, 3 } |-> x + 1]   \* TRUE
SetAsFun({}) = [x \in {} |-> x]                                 \* TRUE
LET F == SetAsFun({ <<1, 2>>, <<1, 3>>, <<1, 4>> }) IN
  \* this is all we can guarantee, when the relation is non-deterministic
  \/ F = [x \in { 1 } |-> 2]
  \/ F = [x \in { 1 } |-> 3]
  \/ F = [x \in { 1 } |-> 4]
```

----------------------------------------------------------------------------

<a name="Cast"></a>

## Interpret a function as a sequence

**Notation:** `FunAsSeq(fn, maxLen)`

**LaTeX notation:** `FunAsSeq(fn, maxLen)`

**Arguments:** Two arguments. The first is a function, the second is an integer.

**Apalache type:** `(Int -> a, Int) => Seq(a)`, for some type `a`

**Effect:** The expression `FunAsSeq(fn, maxLen)` evaluates to the sequence `<< fn[1], ..., fn[maxLen] >>`.
At the level of Apalache static analysis, `FunAsSeq` indicates type-casting a function type `Int -> a` to a sequence type `Seq(a)`, since one cannot use function constructors to define a sequence in Apalache otherwise.

**Determinism:** Deterministic.

**Errors:** 
If `fn` is not a function of the type `Int -> a` or if `maxLen` is not an integer, Apalache statically reports a type error. Additionally, if it is not the case that `1..maxLen \subseteq DOMAIN fn`, the result is undefined.

**Example in TLA+:**

```tla
Head( [ x \in 1..5 |-> x * x ] )                \* 1 in TLC, type error in Apalache
FunAsSeq( [ x \in 1..5 |-> x * x ], 3 )         \* <<1,4,9>>
Head( FunAsSeq( [ x \in 1..5 |-> x * x ], 3 ) ) \* 1
FunAsSeq( <<1,2,3>>, 3 )                        \* <<1,2,3>> in TLC, type error in Apalache
FunAsSeq( [ x \in {0,42} |-> x * x ], 3 )       \* UNDEFINED
```

**Example in Python:**

```python
def funAsSeq(f,imax):
  # f === { x:f(x) | x \in Dom(f) }
  return[f.get(i) for i in range(1,imax+1)]
def boundedFn(f, dom):
  return { x:f(x) for x in dom } 
f = boundedFn( lambda x: x*x, range(1,6) ) # [ x \in 1..5 |-> x * x ]
g = boundedFn( lambda x: x*x, {0,42} )     # [ x \in {0,42} |-> x * x ]
>>> f[1]                                   # Head( [ x \in 1..5 |-> x * x ] )  
1
>>> funAsSeq(f, 3)                         # FunAsSeq( [ x \in 1..5 |-> x * x ], 3 ) 
[1,4,9]
>>> funAsSeq(f, 3)[1]                      # Head( FunAsSeq( [ x \in 1..5 |-> x * x ], 3 ) )
1
>>> funAsSeq( g, 3 )                       # FunAsSeq( [ x \in {0,42} |-> x * x ], 3 )
[None, None, None]
```

<a name="Skolem"></a>
## Skolemization Hint

**Notation:** `Skolem(e)`

**LaTeX notation:** `Skolem(e)`

**Arguments:** One argument. Must be an expression of the form `\E x \in S: P`.

**Apalache type:** `(Bool) => Bool`

**Effect:** The expression `Skolem(\E x \in S: P)` provides a hint to Apalache, that the existential quantification may be skolemized. It evaluates to the same value as `\E x \in S: P`.

**Determinism:** Deterministic.

**Errors:** 
If `e` is not a Boolean expression, throws a type error. If it is Boolean, but not an existentially quantified expression, throws a `StaticAnalysisException`.

**Note:**
This is an operator produced internally by Apalache. You may see instances of this operator, when reading the `.tla` side-outputs of various passes. Manual use of this operator is discouraged and, in many cases, not supported.

**Example in TLA+:**

```tla
Skolem( \E x \in {1,2}: x = 1 ) \* TRUE
Skolem( 1 )                     \* 1 in TLC, type error in Apalache
Skolem( TRUE )                  \* TRUE in TLC, error in Apalache
```

<a name="Expand"></a>
## Set expansion

**Notation:** `Expand(S)`

**LaTeX notation:** `Expand(S)`

**Arguments:** One argument. Must be either `SUBSET SS` or `[T1 -> T2]`.

**Apalache type:** `(Set(a)) => Set(a)`, for some `a`.

**Effect:** The expression `Expand(S)` provides instructions to Apalache, that the large set `S` (powerset or set of functions) should be explicitly constructed as a finite set, overriding Apalache's optimizations for dealing with such collections. It evaluates to the same value as `S`.

**Determinism:** Deterministic.

**Errors:** 
If `e` is not a set, throws a type error. If the expression is a set, but is not of the form `SUBSET SS` or `[T1 -> T2]`, throws a `StaticAnalysisException`.

**Note:**
This is an operator produced internally by Apalache. You may see instances of this operator, when reading the `.tla` side-outputs of various passes. Manual use of this operator is discouraged and, in many cases, not supported.

**Example in TLA+:**

```tla
Expand( SUBSET {1,2} ) \* {{},{1},{2},{1,2}}
Expand( {1,2} )        \* {1,2} in TLC, error in Apalache
Expand( 1 )            \* 1 in TLC, type error in Apalache
```

<a name="ConstCard"></a>
## Cardinality Hint

**Notation:** `ConstCardinality(e)`

**LaTeX notation:** `ConstCardinality(e)`

**Arguments:** One argument. Must be an expression of the form `Cardinality(S) >= k`.

**Apalache type:** `(Bool) => Bool`

**Effect:** The expression `ConstCardinality(Cardinality(S) >= k)` provides a hint to Apalache, that `Cardinality(S)` is a constant, allowing Apalache to encode the constraint `e` without attempting to dynamically encode `Cardinality(S). It evaluates to the same value as `e`.

**Determinism:** Deterministic.

**Errors:** 
If `S` is not a Boolean expression, throws a type error. If it is Boolean, but not an existentially quantified expression, throws a `StaticAnalysisException`.

**Note:**
This is an operator produced internally by Apalache. You may see instances of this operator, when reading the `.tla` side-outputs of various passes. Manual use of this operator is discouraged and, in many cases, not supported.

**Example in TLA+:**

```tla
Skolem( \E x \in {1,2}: x = 1 ) \* TRUE
Skolem( 1 )                     \* 1 in TLC, type error in Apalache
Skolem( TRUE )                  \* TRUE in TLC, error in Apalache
```

