
<a name="recursion"></a>
## Recursive operators and functions

**We are going to remove support for recursive operators and functions soon.
See [Folding sets and sequences](./folds.md).**

**WARNING:** In our experience, it is hard to check recursive operators and
functions in Apalache:

  - Recursive operators need additional annotations.
  - Resursive operators and functions usually apply `CHOOSE`, which
    is hard to implement faithfully without blowing up the SMT encoding.

Hence, we recommend using the operators `FoldSet` and `FoldSeq`:

```tla
{{#include ../../../../src/tla/Apalache.tla:72:93}}
```

These operators are treated by Apalache in a more efficient manner than
recursive operators. They are always terminating and thus do not require an
annotation that specifies an upper bound on the number of operator iterations.
We are preparing a tutorial on this topic.

**See [Folding sets and sequences](./folds.md).**

<a name="rec-op"></a>
### Recursive operators

In the preprocessing phase, Apalache replaces every application of a user
operator with its body. We call this process "operator inlining".
This cannot be done for recursive operators, for two reasons:

 1. A recursive operator may be non-terminating (although a non-terminating
    operator is useless in TLA+);

 1. A terminating call to an operator may take an unpredicted number of iterations.

However, in practice, when one fixes specification parameters (that is,
`CONSTANTS`), it is usually easy to find a bound on the number of operator
iterations. For instance, consider the following specification:

```tla
{{#include ../../../../test/tla/Rec6.tla::}}
```

It is clear that the expression `Sum(S)` requires the number of iterations that
is equal to `Cardinality(S) + 1`. Moreover, the expression `set \subseteq
1..N` is an invariant, and thus every call `Sum(set)` requires up to `N+1`
iterations.

When we can find an upper bound on the number of iterations, Apalache can
unroll the recursive operator up to this bound. To this end, we define two
additional operators. For instance:

```tla
{{#include ../../../../test/tla/MC_Rec6.tla::}}
```

In this case, Apalache unrolls every call to `Sum` exactly `UNROLL_TIMES_Sum`
times, that is, four times. On the default branch, Apalache places
`UNROLL_DEFAULT_Sum`, that is, 0.

All recursively defined operators should follow this convention where, for every such operator `Oper`, the user defines both `UNROLL_TIMES_Oper`, which expands to a positive integer value, and `UNROLL_DEFAULT_Oper`, which expands to some default value `Oper(args*)` should take, if the computation would require more than `UNROLL_TIMES_Oper` recursive calls.
At present, we only support literals (e.g. `4`) or primitive arithmetic expressions (e.g. `2 + 2`) in the body of `UNROLL_TIMES_Oper`.

<a name="rec-fun"></a>

#### Recursive functions

Apalache offers limited support for recursive functions. However, read the
warning below on why you should not use recursive functions. The restrictions
are as follows:

 1. Apalache supports recursive functions that return an integer or a Boolean.

 1. As Apalache's simple type checker is not able to find the type of a
recursive function, all uses of a recursive function should come with a type
annotation.

 1. As in TLC, the function domain must be a finite set.

The example below shows a recursive function that computes the factorial of `n`.


```tla
{{#include ../../../../test/tla/Rec8.tla::}}
```

Check other examples in
[`test/tla`](https://github.com/informalsystems/apalache/tree/unstable/test/tla) that
start with the prefix `Rec`.

**Why you should avoid recursive functions.** Sometimes, recursive functions
concisely describe the function that you need. The nice examples are the
factorial function (see above) and Fibonacci numbers (see
[Rec3](https://github.com/informalsystems/apalache/blob/unstable/test/tla/Rec3.tla)).
However, when you define a recursive function over sets, the complexity gets
ugly really fast.

Consider the example
[Rec9](https://github.com/informalsystems/apalache/blob/unstable/test/tla/Rec9.tla),
which computes set cardinality. Here is a fragment of the spec:

```tla
{{#include ../../../../test/tla/Rec9.tla:19:32}}
```

Since we cannot fix the order, in which the set elements are evaluated, we
define function `Card` over `SUBSET NUMS`, that is, all possible subsets of
`NUMS`. Apalache translates the function in a quantifier-free theory of SMT.
Hence, in this case, Apalache expands `SUBSET NUMS`, so it introduces
`2^|NUMS|` sets! Further, Apalache writes down the SMT constraints for the
domain of `Card`. As a result, it produces `NUMS * 2^|NUMS|` constraints.
As you can see, recursive functions over sets explode quite fast.

It is usually a good idea to use recursive operators over sets rather than
recursive functions. The downside is that you have to provide an upper bound on
the number of the operator iterations. The upside is that recursive operators
are usually unrolled more efficiently. (If they contain only constant
expressions, they are even computed by the translator!) For instance, set
cardinality does not require `2^|NUMS|` constraints, when using a recursive
operator.
