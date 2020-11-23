# Functions

[[Back to all operators]](./standard-operators.md)

Functions is probably the second most used TLA+ data structure after sets. TLA+
functions are not like functions in programming languages. In programming
languages, functions contain code that calls other functions. Although it is
technically possible to use functions when constructing a function in TLA+,
functions are used like tables or dictionaries. For instance, in [Two-phase
commit](https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla),
the function `rmState` stores the transaction state for each process:

```tla
"process1",  "working"
"process2",  "aborted"
"process3",  "prepared"
```

In the above table, the first column is the value of the function argument,
while the second column is the function result. The important property of this
table is that the no value appears in the first column more than once, so
*every argument value is assigned at most one result value*.

Importantly, every function comes with the set of arguments, on which it is
defined. This set is called the function domain.  There is even a special
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

Note that this function efficiently defines an infinite table, as the set `Int`
is infinite. Both TLC and Apalache would give up on a function with an infinite
domain. (Though in the above example, it is obvious that we could treat the
function symbolically, without enumerating all of its elements.)

Another way to construct a function is to *non-deterministically* pick one
from the set of all functions, e.g.:

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

**Types.** In pure TLA+, functions are free to mix whatever values in its
domain. See the example below:

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
Moreover, the elements of the function domain must have the same type.
A general function must return the values of the same type. This is enforced
by the type checker.

In this sense, the type restrictions of Apalache are similar to those for the
generic collections of Java and Scala.  As a result, the type checker in
Apalache rejects the three above examples.

----------------------------------------------------------------------------

## Operators

In the Python examples, we are using the package [frozendict], to produce an
immutable dictionary.

### Function constructor

**Notation:** `[ x \in S |-> e ]` or `[ x \in S, y \in T |-> e ]`, or more
arguments

**LaTeX notation:** ![fun-ctor](./img/fun-ctor.png)

**Arguments:** At least three arguments: a variable name (or a tuple of names,
see **Advanced syntax**), a set, and a mapping expression. Instead of one
variable and one set, you can use multiple variables and multiple sets.

**Effect:** Produce the set that contains the values of the expressions `e_1,
..., e_n`, in no particular order, and only these values. If `n = 0`, the
empty set is constructed.

**Effect:** We give the semantics for one argument.  We write a sequence of
steps to ease the understanding.  This operator constructs a function `f` of
the domain `S` as follows.  For every element `elem` of `S`, do the following:
 
 1. Bind the element `elem` to variable `x`,
 2. Compute the value of `e` under the binding `[x |-> elem]` and store it
    in a temporary variable called `result`.
 3. Store that `f` returns `result` when called with `elem` as the argument.

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

** Advanced syntax:** Instead of a single variable `x`, one can use the tuple
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


[Control Flow and Non-determinism]: ./control-and-nondeterminism.md
[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=learning.html#book
[frozendict]: https://pypi.org/project/frozendict/
