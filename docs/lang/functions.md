# Functions

[[Back to all operators]](./standard-operators.md)

Functions are probably the second most used TLA+ data structure after sets. TLA+
functions are not like functions in programming languages. In programming
languages, functions contain code that calls other functions. Although it is
technically possible to use functions when constructing a function in TLA+,
functions are more often used like tables or dictionaries: they are simple maps from a set of inputs to a set of outputs. For instance, in
[Two-phase commit], the function `rmState` stores the transaction state for
each process:

```tla
"process1",  "working"
"process2",  "aborted"
"process3",  "prepared"
```

In the above table, the first column is the value of the function argument,
while the second column is the function result. An important property of this
table is that no value appears in the first column more than once, so
*every argument value is assigned at most one result value*.

Importantly, every function is defined in terms of the set of arguments over which it is
defined. This set is called the function's _domain_.  There is even a special
operator `DOMAIN f`, which returns the domain of a function `f`.

In contrast to TLA+ operators, _TLA+ functions are proper values_, so they can be
used as values in more complex data structures.

**Construction.** Typically, the predicate `Init` constructs a function that
maps all elements of its domain to a default value.
In the example below we map the set `{ "process1", "process2", "process3" }`
to the value "working":

```tla
Init ==
  rmState = [ p \in { "process1", "process2", "process3" } |-> "working" ]
```

In general, we can construct a function by giving an expression that shows us
how to map every argument to the result:

```tla
  [ fahrenheit \in Int |-> (fahrenheit - 32) * 5 \div 9 ]
```

Note that this function effectively defines an infinite table, as the set `Int`
is infinite. Both TLC and Apalache would give up on a function with an infinite
domain. (Though in the above example, it is obvious that we could treat the
function symbolically, without enumerating all of its elements.)

Another way to construct a function is to *non-deterministically* pick one
from a set of functions, e.g.:

```tla
Init ==
    \E f \in [ { "process1", "process2", "process3" } ->
                    { "working", "prepared", "committed", "aborted" } ]:
        rmState = f
```

In the above example we are not talking about one function that is somehow
initialized "by default". Rather, we say that `rmState` can be set to an
arbitrary function that receives arguments from the set `{ "process1",
"process2", "process3" }` and returns values that belong to the set `{
"working", "prepared", "committed", "aborted" }`. As a result, TLC has to
enumerate all possible functions that match this constraint. On contrary,
Apalache introduces one instance of a function and restricts it with the
symbolic constraints. So it efficiently, considers all possible functions
without enumerating them. However, this trick only works with existential
quantifiers. If you use a universal quantifier over a set of functions,
both TLC and Apalache unfold this set.

**Immutability**. As you can see, TLA+ functions are similar to [dictionaries
in Python](https://docs.python.org/3/library/stdtypes.html#dict) and [maps in
Java](https://docs.oracle.com/javase/8/docs/api/java/util/Map.html) rather than
to normal functions in programming languages. However, *TLA+ functions are
immutable*. Hence, they are even closer to immutable maps in Scala.  As in the
case of sets, you do not need to define hash or equality, in order to use
functions.

If you like to update a function, you have to produce another function and
describe how it is different from the original function. Luckily, TLA+ provides
you with operators for describing these updates in a compact way: By using the
function constructor (above) and by using `EXCEPT`. For instance, to produce a
new function from `rmState`, we write the following:

```tla
  [ rmState EXCEPT !["process3"] = "committed" ]
```

This new function is like `rmState`, except that it returns `"committed"`
on the argument `"process3"`:

```tla
"process1",  "working"
"process2",  "aborted"
"process3",  "committed"
```

_Importantly, you cannot extend the function domain by using `EXCEPT`._
For instance, the following expression produces the function that is
equivalent to `rmState`:

```tla
  [ rmState EXCEPT !["process10"] = "working" ]
```

**Types.** In pure TLA+, functions are free to mix values of different types in their domains. 
See the example below:

```tla
  [ x \in { 0, "FALSE", FALSE, 1, "TRUE", TRUE } |->
        IF x \in { 1, "TRUE", TRUE}
        THEN TRUE
        ELSE FALSE
  ]
```

TLA+ functions are also free to return any kinds of values:

```tla
  [ x \in { 0, "FALSE", FALSE, 1, "TRUE", TRUE } |->
    CASE x = 0 -> 1
      [] x = 1 -> 0
      [] x = "FALSE" -> "TRUE"
      [] x = "TRUE" -> "FALSE"
      [] x = FALSE -> TRUE
      OTHER -> FALSE
  ]
```

As in case of [sets](./sets.md), TLC restricts function domains to comparable
values. See Section 14.7.2 of [Specifying Systems]. So, TLC rejects the two
examples that are given above.

However, functions in TLC are free to return different kinds of values:

```tla
  [ x \in { 1, 2 } |->
                        IF x = 1 THEN FALSE ELSE 3 ]  
```

This is why, in pure TLA+ and TLC, records, tuples, and sequences are just
functions over particular domains (finite sets of strings and finite sets
of integers).

Apalache enforces stricter types. It has designated types for all four
data structures: general functions, records, tuples, and sequences.
Moreover, all elements of the function domain must have the same type.
A general function must return the values of the same type. This is enforced
by the type checker.

In this sense, the type restrictions of Apalache are similar to those for the
generic collections of Java and Scala.  As a result, the type checker in
Apalache rejects the three above examples.

----------------------------------------------------------------------------

## Operators

In the Python examples, we are using the package [frozendict], to produce an
immutable dictionary.

----------------------------------------------------------------------------

<a name="funCtor"></a>
### Function constructor

**Notation:** `[ x \in S |-> e ]` or `[ x \in S, y \in T |-> e ]`, or more
arguments

**LaTeX notation:** ![fun-ctor](./img/fun-ctor.png)

**Arguments:** At least three arguments: a variable name (or a tuple of names,
see **Advanced syntax**), a set, and a mapping expression. Instead of one
variable and one set, you can use multiple variables and multiple sets.

**Effect:** We give the semantics for one argument.  We write a sequence of
steps to ease the understanding.  This operator constructs a function `f` of
the domain `S` as follows.  For every element `elem` of `S`, do the following:
 
 1. Bind the element `elem` to variable `x`,
 2. Compute the value of `e` under the binding `[x |-> elem]` and store it
    in a temporary variable called `result`.
 3. Set `f[elem]` to `result`.

Of course, the semantics of the function constructor in [Specifying Systems]
does not require us to compute the function at all. However, we believe that
it helps you to see that there is a way to compute this data structure, alas,
this way is very straightforward.

If the function constructor introduces multiple variables, then the constructed
function maps a tuple to a value. See **Example**.

**Determinism:** Deterministic.

**Errors:** Pure TLA+ does not restrict the function domain and the mapping
expression. They can be any
combination of TLA+ values: Booleans, integers, strings, sets, functions, etc.

TLC accepts function domains of comparable values. For
instance, two integers are comparable, but an integer and a set are not
comparable. See Section 14.7.2 of [Specifying Systems].

Apalache goes further: It requires the function domain to be well-typed (as a
set), and it requires the mapping expression `e` to be well-typed. If this
is not the case, the type checker flags an error.

**Advanced syntax:** Instead of a single variable `x`, one can use the tuple
syntax to unpack variables from a Cartesian product, see [Tuples](./tuples.md).
For instance, one can write `[ <<x, y>> \in S |-> x + y ]`. In this case, for
every element `e` of `S`, the variable `x` is bound to `e[1]` and `y` is bound
to `e[2]`. The function constructor maps the tuples from `S` to the values
that are computed under such a binding.

**Example in TLA+:**

```tla
  [ x \in 1..3 |-> 2 * x ]  \* a function that maps 1, 2, 3 to 2, 4, 6
  [ x, y \in 1..3 |-> x * y ]
    \* a function that maps <<1, 1>>, <<1, 2>>, <<1, 3>>, ..., <<2, 3>>, <<3, 3>>
    \* to 1, 2, 3, ..., 6, 9
  [ <<x, y>> \in 1..3 \X 4..6 |-> x + y ]
    \* a function that maps <<1, 4>>, <<1, 5>>, <<1, 6>>, ..., <<2, 6>>, <<3, 6>>
    \* to 5, 6, 7, ..., 8, 9
  [ n \in 1..3 |->
      [ i \in 1..n |-> n + i ]]
    \* a function that maps a number n from 1 to 3
    \* to a function from 1..n to n + i. Like an array of arrays.
```

**Example in Python:** TLA+ functions are immutable, so we are using [frozendict]:

```python
  X = frozenset({ 1, 2, 3 })
  frozendict({ x: 2 * x for x in X })
  frozendict({ (x, y): x * y for x in X for y in X })
  Y = frozenset({ 4, 5, 6 })
  XY = frozenset((x, y) for x in X for y in Y)
  frozendict({ (x, y): x + y  for (x, y) in XY })
```

----------------------------------------------------------------------------

<a name="funSetCtor"></a>
### Function set constructor

**Notation:** `[ S -> T ]`

**LaTeX notation:** ![funset](./img/funset.png)

**Arguments:** Two arguments. Both have to be sets. Otherwise, the result is
undefined.

**Effect:** This operator constructs the set of all possible functions that
have `S` as their domain, and for each argument `x \in S` return a value `y \in
T`.

Note that if one of the sets is infinite, then the set `[S -> T]` is infinite
too. TLC flags an error, if `S` or `T` are infinite. Apalache flags an error,
if `S` is infinite. But when Apalache does not have to explicitly construct `[S
-> T]`, it may accept infinite `T`. For instance:

```tla
  \E f \in [ 1..3 -> 4..6]:
    ...
```

**Determinism:** Deterministic.

**Errors:** In pure TLA+, if `S` and `T` are not sets, then `[S -> T]`
is undefined. If `S` or `T` are not sets, TLC flags a model checking error.
Apalache flags a static type error.

**Example in TLA+:**

```tla
  [ 1..3 |-> 1..100 ]
    \* the set of functions that map 1, 2, 3 to values from 1 to 100
  [ Int -> BOOLEAN ]
    \* The infinite set of functions that map every integer to a Boolean.
    \* Error in TLC.
```

**Example in Python:** We do not give here the code that enumerates all
functions. It should be similar in spirit to [subset.py](./examples/subset.py),
but it should enumerate strings over the alphabet of `0..(Cardinality(T) - 1)`
values, rather than over the alphabet of 2 values.

<a name="funApp"></a>
### Function application

**Notation:** `f[e]` or `f[e_1, ..., e_n]`

**LaTeX notation:** `f[e]` or `f[e_1, ..., e_n]`

**Arguments:** At least two arguments. The first one should be a function,
the other arguments are the arguments to the function. Several arguments
are treated as a tuple. For instance, `f[e_1, ..., e_n]` is a shorthand for
`f[<<e_1, ..., e_n>>]`.

**Effect:** This operator evaluates as follows:

 - If `e \in DOMAIN f`, then `f[e]` evaluates to the value that function
 `f` associates with the value of `e`.
 - If `e \notin DOMAIN f`, then the value is undefined.

**Determinism:** Deterministic.

**Errors:** When `e \notin DOMAIN f`, TLC flags a model checking error.

When `e` has the type incompatible with the type of `DOMAIN f`, Apalache flags
a type error. When `e \notin DOMAIN f`, Apalache assigns some type-compatible
value to `f[e]`, but does not report any error. This is not a bug in Apalache,
but the feature of the SMT encoding. Usually, an illegal access surfaces
somewhere, when checking a specification.  If you like to detect an access
outside of the function domain, instrument your code with an additional state
variable.

**Example in TLA+:**

```tla
  [x \in 1..10 |-> x * x][5]                \* 25
  [x \in 1..3, y \in 1..3 |-> x * y][2, 2]
    \* Result = 4. Accessing a two-dimensional matrix by a pair
  [ n \in 1..3 |->
      [ i \in 1..n |-> n + i ]][3][2]
    \* The first access returns a function, the second access returns 5.
  [x \in 1..10 |-> x * x][100]              \* model checking error in TLC,
                                            \* Apalache produces some value
```

**Example in Python:**

```python
  S10 = frozenset(range(1, 10 + 1))
  # TLA: [x \in 1..10 |-> x * x]
  f1 = frozendict({ x: x * x for x in S10 })
  f1[5]         # 25
  S3 = frozenset({ 1, 2, 3 })
  # TLA: [x, y \in 1..3 |-> x * y]
  f2 = frozendict({ (x, y): x * y for x in S3 for y in S3 })
  f2[(2, 2)]    # 4
  # TLA: [ n \in 1..3 |-> [ i \in 1..n |-> n + i ]]
  f3 = frozendict({
    n: frozendict({
      i: n + i
        for i in frozenset(range(1, n + 1))
    })
        for n in S3
  })
  f3[3][2]
```

----------------------------------------------------------------------------

<a name="except"></a>
### Function replacement

**Notation:** `[f EXCEPT ![a_1] = e_1, ..., ![a_n] = e_n]`

**LaTeX notation:** `[f EXCEPT ![a_1] = e_1, ..., ![a_n] = e_n]`

**Arguments:** At least three arguments. The first one should be a function,
the other arguments are interleaved pairs of argument expressions and value
expressions.

**Effect:** This operator evaluates to a new function `g` that is constructed
    as follows:

 - Set the domain of `g` to `DOMAIN f`.
 - For every element `b \in DOMAIN f`, do:
   - If `b = a_i` for some `i \in 1..n`, then set `g[b]` to `e_i`.
   - If `b \notin { a_1, ..., a_n }`, then set `g[b]` to `f[b]`.

_Importantly, `g` is a new function, the function `f` is not modified!_

**Determinism:** Deterministic.

**Errors:** When `a_i \notin DOMAIN f` for some `i \in 1..n`,
TLC flags a model checking error.

When `a_1, ..., a_n` are not type-compatible with the type of `DOMAIN f`,
Apalache flags a type error. When `a_i \notin DOMAIN f`, Apalache ignores this
update. This is consistent with the semantics of TLA+ in [Specifying Systems].

**Advanced syntax:** There are three extensions to the basic syntax.

 _Extension 1_. If the function `f` has the domain over tuples, then, similar to
 function application, the expressions `a_1, ..., a_n` can be written without
 the tuple braces `<<...>>`. For example:

```tla
  [ f EXCEPT ![1, 2] = e ]
```

In the above example, the element `f[<<1, 2>>]` is replaced with `e`.
As you can see, this is just syntax sugar.

 _Extension 2_. The operator `EXCEPT` introduces an implicit alias `@`
that refers to the element `f[a_i]` that is going to be replaced:

```tla
  [ f EXCEPT ![1] = @ + 1, ![2] = @ + 3 ]
```

In the above example, the element `f[1]` is replaced with `f[1] + 1`, whereas
the element `f[2]` is replaced with `f[2] + 3`.
This is also syntax sugar.

 _Extension 3_. The advanced syntax of `EXCEPT` allows for chained replacements.
 For example:

```tla
  [ f EXCEPT ![a_1][a_2]...[a_n] = e ]
```

This is syntax sugar for:

```tla
  [ f EXCEPT ![a_1] =
    [ @ EXCEPT ![a_2] =
        ...
            [ @ EXCEPT ![a_n] = e ]]]
```


**Example in TLA+:**

```tla
  LET f1 == [ p \in 1..3 |-> "working" ] IN
  [ f1 EXCEPT ![2] = "aborted" ]
    \* a new function that maps: 1 to "working", 2 to "aborted", 3 to "working"

  LET f2 == [x \in 1..3, y \in 1..3 |-> x * y] IN
  [ f2 EXCEPT ![1, 1] = 0 ]
    \* a new function that maps:
    \*   <<1, 1>> to 0, and <<x, y>> to x * y when `x /= 0` or `y /= 0`
  LET f3 ==  [ n \in 1..3 |-> [ i \in 1..n |-> n + i ]] IN
  [ f3 EXCEPT ![2][2] = 100 ]
    \* a new function that maps:
    \*   1 to the function that maps: 1 to 2
    \*   2 to the function that maps: 1 to 3, 2 to 100
    \*   3 to the function that maps: 1 to 4, 2 to 5, 3 to 6
```

**Example in Python:**

```python
  f1 = frozendict({ i: "working" for i in range(1, 3 + 1) })
  tmp = dict(f1)
  tmp[2] = "aborted"
  g1 = frozendict(tmp)
  # g1 is <frozendict {1: 'working', 2: 'aborted', 3: 'working'}>

  S3 = frozenset({ 1, 2, 3 })
  # TLA: [x, y \in 1..3 |-> x * y]
  f2 = frozendict({ (x, y): x * y for x in S3 for y in S3 })
  tmp = dict(f2)
  tmp[(1, 1)] = 0
  g2 = frozendict(tmp)
  # <frozendict {(1, 1): 0, (1, 2): 2, (1, 3): 3, (2, 1): 2, (2, 2): 4,
  #              (2, 3): 6, (3, 1): 3, (3, 2): 6, (3, 3): 9}>

  # TLA: [ n \in 1..3 |-> [ i \in 1..n |-> n + i ]]
  f3 = frozendict({
    n: frozendict({
      i: n + i
        for i in frozenset(range(1, n + 1))
    })
        for n in S3
  })
  # [ f3 EXCEPT ![2][2] = 100 ]
  tmp = dict(f3[2])
  tmp[2] = 100
  tmp2 = dict(f3)
  tmp2[2] = tmp
  g3 = frozendict(tmp2)
  # <frozendict {1: <frozendict {1: 2}>,
  #              2: {1: 3, 2: 100},
  #              3: <frozendict {1: 4, 2: 5, 3: 6}>}>
```

----------------------------------------------------------------------------

<a name="domain"></a>
### Function domain

**Notation:** `DOMAIN f`

**LaTeX notation:** `DOMAIN f`

**Arguments:** One argument, which should be a function
               (respectively, a record, tuple, sequence).

**Effect:** `DOMAIN f` returns the set of values, on which the function
has been defined, see: Function constructor and Function set constructor.

**Determinism:** Deterministic.

**Errors:** In pure TLA+, the result is undefined, if `f` is not a function
(respectively, a record, tuple, or sequence). TLC flags a model checking error
if `f` is a value that does not have a domain. Apalache flags a type checking
error.


**Example in TLA+:**

```tla
  DOMAIN [ x \in 1..3 |-> 2 * x ]
  \* { 1, 2, 3 }
```

**Example in Python:** 

```python
  X = frozenset({ 1, 2, 3 })
  f = frozendict({ x: 2 * x for x in X })
  frozenset(f.keys())
  # frozenset({1, 2, 3})
```


[Control Flow and Non-determinism]: ./control-and-nondeterminism.md
[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=learning.html#book
[frozendict]: https://pypi.org/project/frozendict/
[Two-phase commit]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla
