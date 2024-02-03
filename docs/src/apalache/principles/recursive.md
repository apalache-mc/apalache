<a name="recursion"></a>
## Recursive operators and functions

While TLA+ allows the use of recursive operators and functions, we have decided to no longer support them in Apalache from version `0.23.1` onward, and suggest the use of fold operators, described in [Folding sets and sequences](./folds.md) instead: 

```tla
{{#include ../../../../src/tla/Apalache.tla:122:127}}

{{#include ../../../../src/tla/Apalache.tla:137:140}}
```

These operators are treated by Apalache in a more efficient manner than
recursive operators. They always take at most `|S|` or `Len(seq)` steps to evaluate and require no additional annotations.

Note that the remainder of this section discusses only recursive operators, for brevity. Recursive functions share the same issues.

### The problem with recursive operators

In the preprocessing phase, Apalache replaces every application of a user-defined operator with its body. We call this process "operator inlining".
This obviously cannot be done for recursive operators, since the process would never terminate. Additionally, even if inlining wasn't problematic, we would still face the following issues when attempting to construct a symbolic encoding: 

 1. A recursive operator may be non-terminating (although a non-terminating
    operator is useless in TLA+);

 2. A terminating call to an operator may take an unpredictable number of iterations.

A note on (2): In practice, when one fixes specification parameters (that is,
`CONSTANTS`), it is sometimes possible to find a bound on the number of operator iterations. For instance, consider the following specification:

```tla
{{#include ../../../../test/tla/Rec6.tla::}}
```

It is clear that the expression `Sum(S)` requires `Cardinality(S)` steps of recursive computation. Moreover, as the unspecified invariant `set \subseteq 1..N` always holds for this specification, every call `Sum(set)` requires up to `N` recursive steps.

### The previously supported approach

Previously, when it was possible to find an upper bound on the number of iterations of an operator `Op`, such as `N` for `Sum` in the example above, Apalache would unroll the recursive operator up to this bound. 
Two additional operators, `UNROLL_DEFAULT_Op` and `UNROLL_TIMES_Op`, were required, for instance:

```tla
{{#include ../../../../test/tla/Rec6.tla:20:21}}
```

With the operators `UNROLL_DEFAULT_Op` and `UNROLL_TIMES_Op`, 
Apalache would internally replace the definition of `Op` with an operator `OpInternal`, that had the following property:
 1. `OpInternal` was non-recursive
 2. If computing `Op(x)` required a recursion stack of depth at most `UNROLL_TIMES_Op`, then `OpInternal(x) = Op(x)`
 3. Otherwise, `OpInternal(x)` would return the value, which would have been produced by the computation of `Op(x)`, if all applications of `Op` while the recursion stack height was `UNROLL_TIMES_Op` returned `UNROLL_DEFAULT_Op` instead of the value produced by another recursive call to `Op`

Unsurprisingly, (3) caused a lot of confusion, particularly w.r.t. the meaning of the value `UNROLL_DEFAULT_Op`. Consider the following example:

```tla
RECURSIVE Max(_)
Max(S) == 
  IF S = {}
  THEN 0
  ELSE 
    LET x == CHOOSE v \in S: TRUE IN
    LET maxRest == Max(S \ {x}) 
    IN IF x < maxRest THEN maxRest ELSE x

```

As computing `Max(S)` requires `|S|` recursive calls, there is no static upper bound to the recursion stack height that works for all set sizes. Therefore, if one wanted to use this operator in Apalache, one would have to guess (or externally compute) a value `N`, such that, _in the particular specification_, `Max` would never be called on an argument, the cardinality of which exceeded `N`, e.g.
```tla
UNROLL_TIMES_Max = 2
```

In this case, Apalache would produce something equivalent to
```tla
MaxInternal(S) ==
  IF S = {}
  THEN 0
  ELSE 
    LET x1 == CHOOSE v \in S: TRUE IN
    LET maxRest1 == 
      IF S \ {x1} = {}
      THEN 0
      ELSE 
        LET x2 == CHOOSE v \in S \ {x1}: TRUE IN
        LET maxRest2 == 
          IF S \ {x1, x2}  = {}
          THEN 0
          ELSE 
            LET x3 == CHOOSE v \in S \ {x1, x2}: TRUE IN
            LET maxRest3 == UNROLL_DEFAULT_Max 
            IN IF x3 < maxRest3 THEN maxRest3 ELSE x3
        IN IF x2 < maxRest2 THEN maxRest2 ELSE x2
    IN IF x1 < maxRest1 THEN maxRest1 ELSE x1
```

In this case, `MaxInternal({1,42}) = 42 = Max({1,42})`, by property (2) as expected, but `MaxInternal(1..10)` can be any one of 
`3..10 \union {UNROLL_DEFAULT_Max}` (depending on the value of 
`UNROLL_DEFAULT_Max` and the order in which elements are selected by `CHOOSE`), by property (3).

So how does one select a sensible value for `UNROLL_DEFAULT_Op`? The problem is, one generally cannot. 
In the `Max` case, one could pick a "very large" `N` and then assume that `Max` computation has "failed" (exceeded the `UNROLL_TIMES_Max` recursion limit) if the result was ever equal to `N`, though "very large" is of course subjective and gives absolutely no guarantees that `Max` won't be called on a set containing some element `M > N`.

As the recursion becomes more complex (e.g. non-primitive or non-tail), attempting to implement a sort of "monitor" via default values quickly becomes impractical, if not impossible.

Fundamentally though, it is very easy to accidentally either introduce spurious invariant violations, or hide actual invariant violations by doing this. For instance, in a specification with 
```tla
UNROLL_DEFAULT_Max = 42
UNROLL_TIMES_Max = 2

Inv == \A n \in 10..20: Max(1..n) = 42
```

Apalache could "prove" `Inv` holds, as it would rewrite this `Inv` to 

```
\A n \in 10..20: MaxInternal(1..n) = 99
```

and `MaxInternal(1..n)` evaluates to `99` for all `n \in 3..99` (and might still evaluate to `99` for `n > 99`, based on the `CHOOSE` order), despite the fact that `Max(1..n) = n` in the mathematical sense.

Consider now the much simpler alternative:
```tla
NonRecursiveMax(S) == 
  LET Max2(a,b) == IF a < b THEN b ELSE a IN
  ApaFoldSet(Max2, 0, S) 
```

In this case, the user doesn't have to think about defaults (aside from the empty-set case), or recursion, as `ApaFoldSet` ensures `|S|`-step "iteration". As an additional benefit, one also doesn't need to use `CHOOSE` to select elements this way.

So ultimately, the reasons for abandoning support for recursive operators boils down to the following:
  - **In the vast majority of cases, equivalent functionality can be achieved by using `ApaFoldSet` or `ApaFoldSeqLeft`**
  - `UNROLL_TIMES_Op` is hard to determine, or doesn't exist statically,
  - `UNROLL_DEFAULT_Op` is hard to determine,
  - Apalache doesn't have runtime evaluation of recursion, so it can't natively determine when a call to a recursive `Op` would have required more than `UNROLL_TIMES_Op` steps
  - The use of recursive operators produces unpredictable results, particularly when used in invariants