Folding in a nutshell
==========================

Apalache natively implements two operators users might be familiar with from the community modules or functional programming. Those operators are `FoldSet` and `FoldSeq`. This brief introduction to fold operators highlights the following:

  1. What are the semantics of fold operators?
  1. How do I use these operators in Apalache?
  1. Should I use folding or recursion?
  1. Examples of common operators defined with folds

### Semantics of fold operators

Folding refers to iterative application of a binary operator over a collection. Given an operator `Op`, a base value `b` and a collection of values `C`, folding `Op` over `C` starting with `b` is defined as follows:

  1. If `C` is empty, the resulting value is `b`
  1. If `C` is nonempty, we select an element `x` from `C`. If `C` is a sequence, `x` is the head value, and if `C` is a set, `x` is an arbitrary member. Then, we compute `b2 = Op(b, x)` and take `C2 = C without x` (`Tail(C)` or `C \ {x}` respectively). We continue the process, by computing the fold of `Op` over `C2` starting with `b2`.

Note that this is the definition of a _left fold_ in the literature. Apalache does not implement a right fold.

For example, if `C` is the sequence `<<x,y,z>>`, the result is equal to `Op( Op( Op(b, x), y), z)`. If `C = {x,y}`, the result is either `Op( Op(b, x), y)` or `Op( Op(b, y), x)`. Because the order of elements selected is arbitrary in the case of sets, users should be careful, as the result is only uniquely defined in the case that the operator is both associative (`Op(Op(a,b),c) = Op(a,Op(b,c))`) and commutative (`Op(a,b) = Op(b,a)`).

### Using fold operators in Apalache

The syntax of the fold operators is as follows:

```
\* @type: ( (a, b) => a, a, Set(b) ) => a
FoldSet( operator, base, set )

\* @type: ( (a, b) => a, a, Seq(b) ) => a
FoldSeq( operator, base, seq )
```

As shown by the type signature, Apalache permits a very general form of folding, where the types of the collection elements and the type of the base element/return-type of the operator do not have to match. Again, we urge users to exercise caution when using `FoldSet` with an operator, for which the types `a` and `b` are different, as such operators cannot be commutative or associative, and therefore the result is not guaranteed to be unique and predictable. 

The other component of note is `operator`, the _name_ (not definition) of some binary operator, which is available in this context. The following are examples of valid uses of folds:

```
PlusOne(p,q) == p + q + 1
X == FoldSet( PlusOne, 0, {1,2,3} ) \* X = 9 

X == LET Count(p,q) == p + 1 IN FoldSeq( Count, 0, <<1,2,3>> ) \* X = 3
```

while these next examples are considered invalid:

```
\* LAMBDAS in folds are not supported by Apalache
\* Use a local LET-IN operator instead 
X == FoldSet( LAMBDA p,q: p + q, 0, {1,2,3} ) 

\* Built-in operators cannot be called by name in Apalache
\* Define a LET-IN operator Plus(p,q) == p + q instead
X == FoldSet( + , 0, {1,2,3} )
```

Local LET definitions can also be used as closures:

```
A(x) == LET PlusX(p,q) == p + q + x IN FoldSeq( PlusX, 0, <<1,2,3>> )

X == A(1) \* X = 9
```

### Folding VS recursion

While TLA+ allows users to write arbitrary recursive operators, they are, in our experience, mostly used to implement collection traversals. Consider the following implementations of a `Max` operator, which returns the largest element of a sequence:

```
CONSTANT negInf \* Max(<<>>) = -inf, but TLA+ has no literal for ±inf, so we use it as a constant

RECURSIVE MaxRec(_)
MaxRec(seq) == IF seq = <<>>
               THEN negInf
               ELSE LET tailMax == MaxRec(Tail(seq))
                    IN IF tailMax > Head(seq)
                       THEN tailMax
                       ELSE Head(seq)

MaxFold(seq) == LET Max(p,q) == IF p > q THEN p ELSE q
                IN FoldSeq( Max, negInf, seq )
```

The first advantage of the fold implementation, we feel, is that it is much more clear and concise. It also does not require a termination condition, unlike the recursive case.
One inherent problem of using recursive operators with a symbolic encoding, is the inability to estimate termination.
While it may be immediately obvious to a human, that `MaxRec` terminates after no more than `Len(seq)` steps, automatic termination analysis is, in general, a rather complex and incomplete form of static analysis.
Apalache addresses this by finitely unrolling recursive operators and requires users to provide unroll limits (`UNROLL_LIMIT_MaxRec == ...`), which serve as a static upper bound to the number of recursive re-entries, because in general, recursive operators may take an unpredictable number of steps (e.g. computing the Collatz sequence) or never terminate at all.
Consider a minor adaptation of the above example, where the author made a mistake in implementing the operator:

```
RECURSIVE MaxRec(_)
MaxRec(seq) == IF seq = <<>>
               THEN negInf
               ELSE LET tailMax == MaxRec( seq ) \* forgot Tail!
                    IN IF tailMax > Head(seq)
                       THEN tailMax
                       ELSE Head(seq)
```

Now, `MaxRec` never terminates, but spotting this error might not be trivial at a glance. This is where we believe folds hold the second advantage: `FoldSet` and `FoldSeq` *always terminate* in `Cardinality(set)` or `Len(seq)` steps, and each step is simple to describe, as it consists of a single operator application.

In fact, the vast majority of the traditionally recursive operators can be equivalently rewritten as folds, for example:
```
RECURSIVE Cardinality(_)
Cardinality(set) == IF set = {}
                    THEN 0
                    ELSE LET x == CHOOSE y \in set: TRUE
                         IN 1 + Cardinality( set \ {x} )

CardinalityFold(set) == LET Count(p,q) == p + 1 \* the value of q, the set element, is irrelevant
                        IN FoldSet( Count, 0, set )
```

Notice that, in the case of sets, picking an arbitrary element `x`, to remove from the set at each step, utilizes the `CHOOSE` operator. This is a common trait shared by many operators that implement recursion over sets. 
Since the introduction of folds, the use of `CHOOSE` in Apalache is heavily discouraged as it is both inefficient, as well as nondeterministic (unlike how `CHOOSE` is defined in TLA+ literature). 

So the third advantage of using folds is the  ability to, almost always, avoid using the `CHOOSE` operator.

The downside of folding, compared to general recursion, is the inability to express non-primitively recursive functions.
For instance, one cannot define the Ackermann function, as a fold. We find that in most specifications, this is not something the users would want to implement anyway, so in practice, we believe it is almost always better to use fold over recursive functions.

### Examples: The versatility of folds

Here we give some examples of common operators, implemented using folds:

```
\*  Sum of all values of a set of integers
Sum(set) == LET Plus(p,q) == p + q IN FoldSet( Plus, 0, set )

\*  Re-implementation of UNION setOfSets
BigUnion(setOfSets) == LET Union(p,q) == p \union q IN FoldSet( Union, {}, setOfSets )

\*  Re-implementation of SelectSeq
SelectSeq(seq, Test(_)) == LET CondAppend(s,e) == IF Test(e) THEN Append(s, e) ELSE s
                           IN FoldSeq( CondAppend, <<>>, seq )

\*  Quantify the elements in S matching the predicate P
Quantify(S, P(_)) == LET CondCount(p,q) == p + IF P(q) THEN 1 ELSE 0
                     IN FoldSet( CondCount, 0, S )

\* The set of all values in seq
Range(seq) == LET AddToSet(S, e) == S \union {e}
              IN LET Range == FoldSeq( AddToSet, {}, seq )

\* Finds the the value that appears most often in a sequence. Returns elIfEmpty for empty sequences
Mode(seq, elIfEmpty) == LET ExtRange == Range(seq) \union {elIfEmpty}
                        IN LET CountElem(countersAndCurrentMode, e) ==
                             LET counters == countersAndCurrentMode[1]
                                 currentMode == countersAndCurrentMode[2]
                             IN LET newCounters == [ counters EXCEPT ![e] == counters[e] + 1 ]
                                IN IF newCounters[e] > newCounters[currentMode]
                                   THEN << newCounters, e >>
                                   ELSE << newCounters, currentMode >>
                           IN FoldSeq( CountElem, <<[ x \in ExtRange |-> 0 ], elIfEmpty >>, seq )[2]

\* Returns TRUE iff fn is injective
IsInjective(fn) == 
  LET SeenBefore( seenAndResult, e ) == 
    IF fn[e] \in seenAndResult[1]
    THEN [ seenAndResult EXCEPT ![2] = FALSE ]
    ELSE [ seenAndResult EXCEPT ![1] = seenAndResult[1] \union {fn[e]} ]
  IN FoldSet( SeenBefore, << {}, TRUE >>, DOMAIN fn )[2]
```

For the sake of comparison, we rewrite the above operators using recursion, `CHOOSE` or quantification:

```
RECURSIVE Sum(_)
Sum(S) == IF S = {} 
          THEN 0
          ELSE LET x == CHOOSE y \in S : TRUE
               IN  x + Sum(S \ {x})

RECURSIVE BigUnion(_)
BigUnion(setOfSets) == IF setOfSets = {} 
                       THEN {}
                       ELSE LET S == CHOOSE x \in setOfSets : TRUE
                            IN  S \union BigUnion(setOfSets \ {x})

RECURSIVE SelectSeq(_,_)
SelectSeq(seq, Test(_)) == IF seq = <<>>
                           THEN <<>>
                           ELSE LET tail == SelectSeq(Tail(seq), Test)
                                IN IF Test( Head(seq) )
                                   THEN <<Head(seq)>> \o tail
                                   ELSE tail

RECURSIVE Quantify(_,_)
Quantify(S, P(_)) == IF S = {} 
                     THEN 0
                     ELSE LET x == CHOOSE y \in S : TRUE
                          IN (IF P(x) THEN 1 ELSE 0) + Quantify(S \ {x}, P) 

RECURSIVE Range(_)
Range(seq) == IF seq = <<>>
              THEN {}
              ELSE {Head(seq)} \union Range(Tail(seq))

Mode(seq, elIfEmpty) == IF seq = <<>>
                        THEN elIfEmpty 
                        ELSE LET numOf(p) == Quantify( DOMAIN seq, LAMBDA q: q = p )
                             IN CHOOSE x \in Range(seq): \A y \in Range(seq) : numOf(x) >= numOf(y)

IsInjective(fn) == \A a,b \in DOMAIN fn : fn[a] = fn[b] => a = b
```

In most cases, recursive operators are much more verbose, and the operators using `CHOOSE` and/or quantification mask double iteration (and thus have quadratic complexity). 
For instance, the evaluation of the fold-less `IsInjective` operator actually requires the traversal of all domain pairs, instead of the single domain traversal with fold.
In particular, `Mode`, the most verbose among the fold-defined operators, is still very readable (most LET-IN operators are introduced to improve readability, at the cost of verbosity) and quite efficient, as its complexity is linear w.r.t. the length of the sequence (the mode could also be computed directly, without a sub-call to `Range`, but the example would be more difficult to read), unlike the variant with `CHOOSE` and `\A`, which is quadratic.
