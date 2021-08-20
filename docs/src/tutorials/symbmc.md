# Symbolic Model Checking

This brief introduction to symbolic model checking discusses the following:

  1. State-spaces and transition systems
  1. What is a symbolic state?
  1. What are symbolic traces?
  1. How do I interpret Apalache counterexamples?

## Notation and preliminary definitions
We will be using the following definitions and conventions:

  - Isomorphisms: Sets `A` and `B` are called isomorphic, if there exists a bijective function
  `b \in [A -> B]`.
  - Predicates: Given a set `T`, a _predicate_ over `T` is a function `P \in [T -> BOOLEAN]`, that is, a function `P`, such that `P(t) \in {TRUE, FALSE}` for each `t \in T`.
  - Relations: Predicates over `A \X B` are called _relations_. A relation `R` over `T \X T` is an _equivalence relation_, if the following holds:
    - For all `t \in T`, it is the case that `R(t,t)` (reflexivity).
    - For all `s,t \in T`, `R(s,t)` holds if and only if `R(t,s)` holds (symmetry).
    - For all `r,s,t \in T`, `R(r,s) /\ R(s,t)` implies `R(r,t)` (transititvity).
  - Equivalence classes: An equivalence relation `R` over `T \X T` defines a function `E \in [T -> SUBSET T]`, such that, for each `t \in T`, `E(t) = { t2 \in T: R(t,t2) }`. `E(t)` is called the _equivalence class_ of `t` for `R`, denoted as `[t]_R`.
  - Quotient space: An equivalence relation `R` over `T \X T` defines a _quotient space_, denoted `T // R`, such that `T // R = { [t]_R : t \in T } \subseteq SUBSET T`.
  - Subset-predicate equivalence: For any set `T`, there exists a natural isomorphism between
  `[T -> BOOLEAN]` and `SUBSET T`: Each predicate `P \in [T -> BOOLEAN]` corresponds to the set `{ t \in T: P(t) = TRUE} \in SUBSET T`. For this reason, predicates are often directly identified with the subset they are equivalent to, and we write `P \subseteq T` for brevity.
  - Infix notation: Given a relation `R \in [A \X B -> BOOLEAN]`, we commonly write `a R b` instead of `R(a,b)` (e.g. `a > b` instead of `>(a,b)`).
  - Cartesian product: Given a set `T`, we use `T^2` to refer to `T \X T`. `T^k`, for `k > 2` is defined similarly.
  - Common sets: We use the shorthand `Z` to refer to the set of all integers, and `N` to refer to the set of all naturals, i.e. `N = {z \in Z: z >= 0}`.

## On state-spaces and transition systems
A TLA+ specification defines a triple `(S,S0,->)`, called a _transition system_. `S` is the _state space_, `S0` is the set of initial states (`S0 \subseteq S`), and `->` is the transition relation, a subset of `S^2`.

### State spaces
The notion of a single state depends on the specification, in particular, on the (number of) variables it declares. If a specification declares 
```tla
VARIABLE A1, A2, A3, ..., Ak
```
then a _state_ is a `k`-field record `[A1 |-> a1, ..., Ak |-> ak]`, where `ai` represents the value of the variable `Ai`, for each `i = 1,...,k`. The state space `S` is then the set of all such `k`-records, i.e. the set of all possible combinations of values that variables may hold.
For brevity, whenever the specification defines exactly one variable, we will treat a state as a single value `a1` instead of the record `[A1 |-> a1]`.

In untyped TLA+, one can think of `S` as `[A1:U, ..., Ak: U]`, which is naturally isomorphic to `U^k`, where `U` is the universe of all TLA+ values. In typed TLA+, such as in Apalache, where variable declarations look like:
```tla
VARIABLE 
  \* @type: T1;
  A1, 
  ..., 
  \* @type: Tk;
  Ak
```
 `S` is the set `[A1: V1, ..., Ak: Vk]`, where `Vi` is the set of all values, which hold the type `Ti`, for each `i = 1,...,k`.
For example, in the specification with
```tla
VARIABLE 
  \* @type: Bool;
  a, 
  \* @type: Bool;
  b
```
The state space is `[x: BOOLEAN,y: BOOLEAN]` when considering types, since each variable can hold one of two boolean values. In the untyped setting, the state space is infinite, and contains all pairs of TLA+ values, so, for example
```
{
  [ x |-> 1, 
    y |-> TRUE ], 
  [ x |-> [z \in 1..5 |-> "a"], 
    y |-> CHOOSE p \in {}: TRUE ]
} \subset S
```

As Apalache enforces a type system,the remainder of this document will assume the typed setting. This assumption does not change any of the definitions. We will also assume that every specification declares an initial-state predicate `Init`, a transition-predicate `Next` and an invariant `Inv` (if not specified, assumed to be `TRUE`). For simplicity, we will also assume that the specification if free of constants, resp. that all of the constants have been initialized.

### Initial states
The second component, `S0`, the set of all initial states, is derived from `S` and `Init`. 
The initial state predicate is a Boolean formula, in which specification-variables appear as free logic variables. 
One can see the operator `Init` as a predicate `S0 \in [S -> BOOLEAN]`, that means that, given a state `s \in S`, the formula obtained by replacing all occurrences of variable names `Ai` in `Init` with the values `s.Ai` (denoted `S0(s)`) is a Boolean formula with no free variables (in a well-typed, parseable specification), which evaluates to either `TRUE` or `FALSE`. By the subset-predicate equivalence, we treat the predicate `S0` as a subset of `S` (as it is equivalent to `{ s \in S: S0(s) = TRUE }`).

For example, given
```tla
VARIABLE 
  \* @type: Int;
  x,
  \* @type: Int;
  y

Init == x \in 3..5 /\ y = 2 
```
we see that `S = [x: Z, y: Z]` and `S0 = { [x |-> 3, y |-> 2], [x |-> 4, y |-> 2], [x |-> 5, y |-> 2] }`.

### Transitions
Similar to `S0`, `->` is derived from `S` and `Next`. If `S0` is a single-argument predicate `S0 \in [S -> BOOLEAN]`, then `->` is a relation `-> \in [S^2 -> BOOLEAN]`. 
`->(s1,s2)` is the formula obtained by replacing all occurrences of variable names `Ai` in `Next` with the values `s1.Ai`, and all occurrences of `Ai'` with `s2.Ai`.
By the same principle of subset-predicate equivalence, we can treat `->` as a subset of `S^2`.
As mentioned in the notation section, it is generally more convenient to use the infix notation
`s1 -> s2` over `->(s1, s2)`. We say that a state `s2` is a _successor_ of the state `s1` if `s1 -> s2`. 

For example, given
```tla
VARIABLE 
  \* @type: Int;
  x,
  \* @type: Int;
  y

Init == x \in 3..5 /\ y = 2 

Next == x' \in { x, x + 1 } /\ UNCHANGED y
```
One can deduce, for any state `[x: a, y: b] \in S`, that it has two successors: `[x: a, y: b]-> [x: a + 1, y: b]` and `[x: a, y: b] -> [x: a, y: b]`.

### Reachable states
Using the above definitions, we can define the set of states reachable in exactly `k`-steps, for `k \in N`, denoted by `R(k)`. We define `R(0) = S0` and for each `k \in N`,
```tla
R(k+1) := { t \in S: \E s \in R(k): s -> t }
```

Similarly, we can define the set of states reachable in _at most_ `k`-steps, denoted `r(k)`, for `k \in N` by
```tla
r(k) = R(0) \union R(1) \union ... \union R(k-1) \union R(k)
```

Finally, we define the et of all _reachable_ states, `R`, as the (infinite) union of all `r(k)`, over `k \in N`:
```tla
R = r(0) \union r(1) \union ...
```

For example, given
```tla
VARIABLE 
  \* @type: Int;
  x,
  \* @type: Int;
  y

Init == x \in 1..3 /\ y = 2

Next == x' = x + 1 /\ UNCHANGED y
```
we can deduce: 
```tla
R(0) = r(0) = S0 = {[x: 1, y: 2],[x: 2, y: 2],[x: 3, y: 2]}

R(1) = {[x: 2, y: 2], [x: 3, y: 2], [x: 4, y: 2]}
r(1) = {[x: 1, y: 2], [x: 2, y: 2], [x: 3, y: 2], [x: 4, y: 2]}

R(2) = {[x: 3, y: 2], [x: 4, y: 2], [x: 5, y: 2]}
r(2) = {[x: 1, y: 2], [x: 2, y: 2], [x: 3, y: 2], [x: 4, y: 2], [x: 5, y: 2]}
```
and so on. We can express this compactly as:
```
R(i) = [x: (i+1)..(i+3), y: {2}],
r(i) = [x: 1..(i+3)    , y: {2}],
R    = [x: N           , y: {2}]`
```

### Finite diameters
We say that a transition system has a _finite diameter_, if there exists a `k \in N`, such that `R = r(k)`.

If such an integer exists then the smallest integer `k`, for which this holds true, is the _diameter_ of the transition system.
In other words, if the transition system `(S,S0,->)` has a finite diameter of `k`, any state that is reachable from a state in `S0`, is reachable in at most `k` transitions. The example above clearly does not have a finite diameter, since `R` is infinite, but `r(k)` is finite for each `k`.

However, the spec
```tla
VARIABLE 
  \* @type: Int;
  x

Init == x = 0 

Next == x' = (x + 1) % 7
```
has a finite diameter (more specifically, a diameter of 6), because:
  
  1. `R = 0..6` (the set of remainders modulo 7), since those are the only values `x'`, which is defined as a `% 7` expression, can take. 
  1. for any `k = 0,...,5`, it is the case that `r(k) = 0..k # R`, so the diameter is not in `{1,...,5}`
  1. for any `k >= 6`, `r(k) = 0..6 = r(6) = R`

### Invariants
Much like `Init`, an invariant operator `Inv` defines a predicate. However, it is not, in general, the case that `Inv` defines a predicate over `S`. There are different cases we can consider, discussed in more detail [here](...). For the purposes of this document, we focus on _state invariants_, i.e. operators which use only unprimed variables and no temporal- or trace- operators. A state invariant operator `Inv` defines a predicate `I` over `S`.
We say that the `I` is an _invariant_ in the transition system, if `R \subseteq I`, that is, for every reachable state `r \in R`, `I(r)` holds true. If `R \ I` is nonempty (i.e., there exists a state `r \in R`, such that `~I(r)`), we refer to elements of `R \ I` as _witnesses_ to invariant violation.

### Goals of model checking
The goal of model checking is to determine whether or not `R \ I` contains a witness. 
The goal of bounded model checking is to determine, given a bound `k`, whether or not `r(k) \ I` contains a witness.

In a transition system with a bounded diameter, one can use bounded model checking to solve the general model checking problem, since `R \ I` is equivalent to `r(k) \ I` for a sufficiently large `k`. In general, if the system does not have a bounded diameter, failing to find a witness in `r(k) \ I` cannot be used to reason about the absence of witnesses in `R \ I`! 

## Explicit-state model checking
The idea behind explicit-state model checking is to simply perform the following algorithm:
  
  Compute `S0` and set `Visited <- {}, ToVisit <- S0`

  1. While `ToVisit # {}`, pick some `s \in ToVisit`: 
    1. If `~I(s)` then terminate, since a witness is found.
    1. If `I(s)` then compute `Successor(s) = { s2 \in S: s -> s2 }`. Set
      ``` 
      Visited <- Visited \union {s}
      ToVisit <- (ToVisit \union Successor(s)) \ Visited
      ```

  1. If `ToVisit = {}` terminate. `R = Visited` and `I` is an invariant.

While simple to describe, there are several limitations of this approach in practice.
The first limitation is the absence of a termination guarantee. More specifically, this algorithm terminates if and only if `R` is finite. For example:
```tla
VARIABLE 
  \* @type: Int;
  x

Init == x = 0
Next == x' = x + 1
```
Defines a states space, for which `R = N`, so the above algorithm never terminates.
Further, it is, in the general case, difficult or impossible to compute `S0` or `Successor(s)`. 
Consider the following specification:
```tla
VARIABLE x

Successor(n) == IF n % 2 = 0 THEN n \div 2 ELSE 3*n + 1 

RECURSIVE kIter(_,_)
kIter(a,k) == IF k <= 0 THEN a ELSE Successor(kIter(a, k-1))

ReachesOne(a) == \E n \in Nat: kIter(a,n) = 1

Init == x \in { n \in Nat: ~ReachesOne(n) }
```
The specification encodes the [Collatz conjecture](...), so computing `S0` is equivalent to proving or disproving the conjecture, which remains an open problem at present. It is therefore unreasonable to expect any model checker to be able to accept such input, despite the fact that the condition is easily describable in first-order logic.
A similar problem occurs in computing `Successor(s)`; the relation between variables `vi` and `vi'` may be given by means of an implicit function or uncomputable expression.

Therefore, most solvers impose the following constraints, which make computing `S0` and `Successor(s)` possible without any sort of specialized solver:
The specification must have the shape
```tla
VARIABLE v1,...,vk

Init == /\ v1 \in F1()
        /\ v2 \in F2(v1)
        ...
        /\ vk \in Fk(v1,...,v{k-1})

Next == /\ CondN(v1,...,vk)
        /\ v1' \in G1(v1,...,vk)
        /\ v2' \in G2(v1,...,vk, v1')
        ...
        /\ vk' \in Gk(v1,...,vk, v1',...,v{k-1}')
```
or some equivalent form, in which variable values in a state can be iteratively computed, one at a time, by means of an explicit formula, which uses only variables computed so far.
For instance,
```tla
VARIABLE x,y

Init == /\ x \in 1..0
        /\ y \in { k \in 1..10, k > x }

Next == \/ /\ x > 5
           /\ x' = x - 1
           /\ y' = x' + 1
        \/ /\ x <= 5
           /\ y' = 5 - x
           /\ x' = x + y'
```

allows the solver to compute both `S0` as well as `Successor(s)`, for any `s`, by traversing the conjunctions in the syntax-imposed order. 

However, even in a situation where states are computable, and `R` is finite, the size of `R` itself might be an issue in practice. We can create specifications of arbitrary size:
```tla
VARIABLE v1,...,vk

Init == /\ v1 = 0
        ...
        /\ vk = 0
Next == \/ /\ v1' = (v1 + 1) % C
           /\ UNCHANGED <<v2,...,vk>>
        \/ /\ v2' = (v2 + 1) % C
           /\ UNCHANGED <<v1,v3,...,vk>>
        ...
        \/ /\ vk' = (vk + 1) % C
           /\ UNCHANGED <<v1,...,v{k-1}>>

```
will have `C^k` distinct states, despite its rather simplistic behavior.

## Symbolic bounded model checking
Much like how the algorithm for explicit-state model checking does not terminate for systems without a finite diameter, we focus only on attempting to model-check systems with bounded diameters. Thus, for a given `k \in N`, we want to find a way to determine if `r(k) \ I` is empty, without testing every single state in `r(k)`.
This method might still find an invariant violation in systems with infinite diameters, if it can occur within the bound `k`, but it is not guaranteed to do so.

The key insight behind symbolic model checking is the following: it is often the case, like in the above specification, that the size of the reachable state space is large, not because of the properties of the specification, but simply because of the constants or sets involved. Consider the example:
```tla
VARIABLE 
  \* @type: Int;
  x

Init == x = 1
Next1 == x' \in 1..9
Next2 == x' \in 1..999999999999

Inv == x < 5
```

The sets of reachable states defined by each `Next` have sizes proportional to the upper bounds of the ranges used. However, to find a violation of the invariant, one merely needs to identify a state in which, for example, `x = 7`, which belongs to both sets. 
It is not necessary, or efficient, to loop over elements in the range and test each one against `Inv` to find a violation, because, depending on the logic fragment `Inv` belongs to, there usually exist external solvers, capable of finding such solutions much faster.

From this perspective, if, for some `k`, we succeeded in finding a predicate `P` over `S`, such that:

  - `P` belongs to a logic fragment, for which an external solver exists
  - `(\E s \in S: P(s)) <=> r(k) \ I # {}`

we can use an external solver to evaluate `P` and find a witness to the violation of `I`, or conclude `r(k) \subseteq I`.

To do this, it is sufficient to find a predicate `Pl` encoding `R(l)`, for each `l \in 0..k`, since:
```
s \in r(k) <=> \/ s \in R(0)
               \/ s \in R(1)
               ...
               \/ s \in R(k)
```

How does one encode `P0`?
```
s \in R(0) <=> s \in S0 <=> S0(s)
```
so `P0(s) = S0(s)`. How about `P1`?
```
s \in R(1) <=> s \in { t \in S | \E s0 \in R(0) : s0 -> t }
           <=> \E s0 \in R(0) : s0 -> s
           <=> \E s0 \in S: P0(s0) /\ s0 -> s
```
so `P1(s) := \E s0 \in S: P0(s0) /\ s0 -> s`

continuing this way, we can determine
```
Pk(s) := \E s{k-1} \in S: P{k-1}(s{k-1}) /\ s{k-1} -> s
```
Which can be expanded to
```
Pk(s) = \E s0,...,s{k-1} \in S: S0(s0) /\ s0 -> s1 /\ s1 -> s2 /\ ... /\ s{k-1} -> s
```

Then, `\E sk \in R(k) \ I` becomes
```
\E s0,...,sk \in S: S0(s0) /\ s0 -> s1 /\ s1 -> s2 /\ ... /\ s{k-1} -> sk /\ ~I(sk)
```

The challenge in designing a symbolic model checker is determining, given TLA+ operators `Init`, `Next` and `Inv`, the encodings of `S0, ->, I` as formulas in logcis supported by some external solvers (e.g. SMT).

### Symbolic states
In an explicit approach, the basic unit of computation is a single state `s \in S`. However, as demonstrated above, symbolic approaches deal with logical formulas. Recall that a state formula, such as `Init` is actually a predicate over `S`, and a predicate is equivalent to a subset of `S`.

Predicates tend to not distinguish between certain concrete states. For instance, the formula
`x < 3` is equally false for both `x = 7` and `x = 70000000`.
Before we define symbolic states, it is time for a short mathematical interlude:
A predicate `P` over `S` naturally defines the following equivalence relation `®_P`: For `a,b \in S`, we say that `®_P(a, b)` holds if `P(a) = P(b)`.
Proving that this relation satisfies the criteria for an equivalence relation is left as an exercise to the reader.
This equivalence relation has only two distinct equivalence classes, since `P(s)` can only be `TRUE` or `FALSE`.
We can therefore think of predicates in the following way: Each predicate `P` slices the 
set `S` into two disjoint subsets, i.e. the equivalence classes of `®_P`.
An alternative equivalent formulation of the above is saying that each predicate `P` defines a quotient space `S // ®_P`, of size `2`.

Why is this relevant? Recall that we have expressed the set of states `R(l)` with the predicate `Pl`, for each `l`. By the above, `Pl` defines an equivalence relation `®_Pl` on S, and consequently, two equivalence classes. 
Each concrete state `s \in S` belongs to exactly one equivalence class `[s]_®_Pl \in (S // ®_Pl)`.
The states in `R(l)` correspond to the equivalence class in which `®_Pl` holds true (i.e. `s \in R(l) <=> [s]_®_Pl = {t \in S: Pl(t) = TRUE}`), and the ones in `S \ R(l)` correspond to the equivalence class in which `®_Pl` is false (i.e. `s \notin R(l) <=> [s]_®_Pl = {t \in S: Pl(t) = FALSE}`).

We define symbolic states in the following way: Given a predicate `P` over `S`, a _symbolic state_ with respect to `P` is an element of `S // ®_P`, where `®_P` is the equivalence relation derived from `P` (i.e. `®_P(a,b) <=> P(a) = P(b)`). 
Recall the subset-predicate equivalence: in this context, a symbolic state, w.r.t. `P` is a predicate, specifically, either `P` or `~P`.

For example, given
```tla
VARIABLE 
  \* @type: Int;
  x,
  \* @type: Int;
  y


Init == x = 1 /\ y = 1 
Next == x' \in 1..5 /\ y \in {0,1}
```

and the predicate `P(s) = s.x < 3`, the symbolic states are 
```tla
[x: {z \in Z: z < 3}, y: Z]
```
and
```tla
[x: {z \in Z: z >= 3}, y: Z]
```

while the symbolic states w.r.t. `R(0)` are 
```
[x: {1}, y: {1}]
```
and
```
[x: Z \ {1}, y: Z \ {1}]
```

The next step is taking a look at granularity: often, a predicate `P` is constructed as a conjunction of other predicates, e.g. `P(s) <=> p1(s) /\ ... /\ pm(s)`. A violation of `P` means a violation of (at least) one of `p1,...pm`, but knowing which one is often beneficial, e.g. because it enables additional analysis.

A collection of predicates `p1,...,pm` over `S` define an equivalence relation `®[p1,...,pm]`in the following way:
For `a,b \in S`, we say that `®[p1,...,pm](a, b)` holds if `<<p1(a),...,pm(a)>> = <<p1(b), ..., pm(b)>>`. Clearly, `®[p1] = ®_p1`.

Since a predicate can only evaluate to one of two values, there exist only two equivalence classes for `®_P`, i.e. only two symbolic states w.r.t. `P`, one is the set of all states for which `®_P` is `TRUE`, and the other is the set of all values for which `®_P` is `FALSE`. In this sense, `S // ®_P` is isomorphic to the set of all binary strings of length 1 (i.e. the set of all Booleans). In the case of `®[p1,...,pm]`, there are `2^m` different `m-tuples` with values from `{TRUE,FALSE}`, so `S // ®[p1,...,pm]` is isomorphic to the set of all binary strings of length `m`. 

What is the relation between `®[p1,...,pm]` and `®_P`, where `P(s) = p1(s) /\ ... /\ pm(s)`?
Clearly, `P(s) = TRUE <=> <<p1(s),...,pm(s)>> = <<TRUE,...,TRUE>>`. 
Consequently, there is one equivalence class in `S // ®_P`, that is equal to
```
C1 = { s \ in S: P(s) = TRUE }
```
and one equivalence class in `S // ®[p1,...,pm]` that is equal to
```
C2 = { s \in S: <<p1(s),...,pm(s)>> = <<TRUE, ..., TRUE>> }
```

They are one and the same, i.e. `C1 = C2`. The difference is, that splitting `P` into `m` components `p1,...,pm` splits the other (unique) equivalence class `C \in { cl \in S // ®_P : cl # C1 }` into `2^m - 1` parts, which are the equivalence classes in `{ cl \in S // ®[p1,...,pm] : cl # C2 }`.

Consequently, we can also define symbolic states with respect to a set of predicates `{p1,...,pm}`, implicitly conjoined, as elements of `S // ®[p1,...,pm]`.
Similarly, by the subset-predicate equivalence, a symbolic state, w.r.t. `{p1,...,pm}` can be viewed as one of
```
p1(s) /\ p2(s) /\ ... /\ pm(s)                  \* = P(s)
~p1(s) /\ p2(s) /\ ... /\ pm(s)                 \* \
p1(s) /\ ~p2(s) /\ ... /\ pm(s)                 \*  |
...                                             \*   > (as a disjunction) = ~P(s) 
~p1(s) /\ ~p2(s) /\ ... /\ ~p{m-1}(s) /\ pm(s)  \*  |
~p1(s) /\ ~p2(s) /\ ... /\ ~p{m-1}(s) /\ ~pm(s) \* /
```

For example, take `p1(s) = s \ in R(k)` and `p2(s) = ~I(s)`. With respect to `p1(s) /\ p2(s)`, there are two symbolic states: one corresponds to the set of all states which are both reachable and in which the invariant is violated, while the other corresponds to the set of all states, which are either not reachable, or in which the invariant holds.
Conversely, with respect to `{p1,p2}`, there are four symbolic states: one corresponds to states which are both reachable and violate the invariant, one corresponds to states which are reachable, but which do not violate the invariant, one corresponds to states which are not reachable, but violate the invariant and the last one corresponds to states which are neither reachable, nor violate the invariant.

### Symbolic traces
Having defined symbolic states, what is then the meaning of a symbolic trace?
In the explicit model, a _trace_ of length `k` is simply a sequence of reachable states 
`s0,..., sk \in S`, such that `s0 \in R(0) /\ ... /\ sk \in R(k)` and `si -> s{i+1}`. 
In the symbolic setting, a _symbolic trace_ is a sequence of symbolic states `C0,...,Ck \in SUBSET S`, such that 
```
C0 \in S // ®_P0 /\ ... /\ Ck \in S // ®_Pk
```

and, for each `i = 0,...k`, it is the case that `Ci = { s \in S: Pi(s) = TRUE }`.
In other words, a symbolic trace is the unique sequence of symbolic states, which correspond to the set of explicit states evaluating to `TRUE` under each of `P0,...,Pk` respectively.

Recall that `P{i+1}(s{i+1})` was defined as `\E si \in S: Pi(si) /\ si -> s{i+1}`.
While, in the explicit case, we needed to enforce the condition `si -> s{i+1}`, in the symbolic case this is already a part of the predicate definition.

For example, consider:
```tla
VARIABLE 
  \* @type: Int;
  x

Init == x \in {0,1}
Next == x' = x + 1
```
a trace of length 2 would be one of `0,1,2` or `1,2,3`. A symbolic trace would be the sequence
```
0..1, 1..2, 2..3
```

<!-- ### Symbolic transitions
Considering the definition of a symbolic state lifts the analysis from `S` to `S // R`, for an equivalence relation `R` derived from a unary predicate `P` over `S`, it should come as little surprise, that symbolic transitions will be defined in terms of `S \X S // R`, for an equivalence relation `R` derived from a binary predicate `P` over `S \X S`.

Let `P` be a binary predicate over `S \X S`. `P` naturally defines a relation `T_P` over `(S \X S) \X (S \X S)` in the following way:
```
T_P(<<s1,s2>>, <<t1,t2>>) <=> P(s1,s2) = P(t1,t2)
```
Note that this is the exact same definition we used in the previous section, up to pattern-matching the domain of the predicate (`S`, in the previous section could be `A \X B` for some `A,B`). -->

In the case of symbolic states, we were particularly interested in symbolic states with respect to predicates that encoded reachability. 
<!-- Here, we take a look at scenarios, where `P(s1,s2)` is `s1 -> s2`. For this reason, a _symbolic transition_ is defined to simply be an element of  `S \X S // T_->`.
Again, in the sense of the predicate-subset equivalence, a symbolic transition is either `->` or its negation.
 -->
Unlike the case of general predicates, the most interesting scenario w.r.t. traces is when a transition relation is presented as a disjunction of transitions, i.e. when 
```
s1 -> s2 <=> \/ t1(s1,s2)
             \/ t2(s1,s2)
             ...
             \/ tm(s1,s2)
```

At the specification level, this is usually the case when one can nondeterministically choose to perform one of `m` actions, and each `t1,...,tm` is an encoding of one such action, which, like `->`, translates to a binary predicate over `S`. 

<!-- A collection of predicates `t1,...,tm` over `S \X S` define an equivalence relation `T_[t1,...,tm]`in the following way:
For `a,b \in S \X S`, we say that `T_[t1,...,tm](a, b)` holds if `\E i \in 1..m : ti(a) = ti(b)`. Clearly, `T_[p1] = T_p1`.

Unsurprisingly, there is a relation between `T_->` and `T_[t1,...,tm]`. There is one equivalence class in `S \X S // T_->`, that is equal to
```
C1 = { <<s1,s2>> \in S \X S: s1 -> s2 = FALSE }
```
and one equivalence class in `S // T_[t1,...,tm]` that is equal to
```
C2 = { <<s1,s2>> \in S \X S: <<t1(s1,s2),...,tm(s1,s2)>> = <<FALSE,...,FALSE>> }
```
They are, again, one and the same, i.e. `C1 = C2`. This time, the equivalence class corresponding to `FALSE` is maintained, while the other is sliced into `2^m - 1`. -->

Instead of a single trace `C1, ..., Ck`, where states in `C{i+1}` are reachable from states in `Ci` via `->`, we want to separate sets of states reachable by each `t1` individually.

<!-- Given a relation `->` and relations `t1,...,tm`, such that `s1 -> s2 <=> t1(s1,s2) \/ ... \/ tm(s1,s2)`, we say that a set `C \in SUBSET S \X S` is a _transition slice_ for `ti`, if `C \in S \X S // T_ti` and for all `<<s1,s2>> \in C`, `ti(s1,s2)` (that is, `C` is the element corresponding to `ti` and not `~ti`).
If we take all slices `C1,...Cm` for `t1,...,tm`, then their union, `C1 \union ... \union Cm`
is exactly equal to the element `C \in S \X S // T_->` corresponding to `->`. -->

Recall that symbolic traces are sequences of symbolic states, implicitly related by `->`, since `R` is defined in terms of `->`. 
We define a symbolic trace decomposition by `t1,...,tm`, in the following way: 
If `t1,...,tm` are relations, such that `s1 -> s2 <=> t1(s1,s2) \/ ... \/ tm(s1,s2)`, the decomposition of a symbolic trace `X0,...,Xk` of length `k` w.r.t. `t1,...,tm` is a set `D = {tr(tau): tau \in [1..k -> 1..m]}` , such that:

  - `tr(tau)` is a _partial symbolic trace_ of length k: `Y0(tau) = X0, Y1(tau),..., Yk(tau)`
  - For each `i = 0,...,k-1`, 
  ```
  Y{i+1}(tau) = { s{i+1} \in X{i+1}: \E si \in Yi(tau) : t{tau(i+1)}(si,s{i+1}) }
  ```

An interesting property to observe is that, for each `i=1,...k`, the sets
`Yi(tau)`, over all possible `tau`, form a decomposition of `Xi`. Concretely:
```
Xi = UNION { Yi(tau): tau \in [1..k -> 1..m] }
```

Less obvious is the fact that, the larger the index `i`, the finer this decomposition becomes.
Consider `i=1`. Since `Y0` is fixed, there are as many different `Y1(tau)` components as there are possible values of `tau(1)`, i.e. `m`. As `Y2` depends on `Y1`, there are as many different components as there are pairs `<<tau(1),tau(2)>>`, i.e. `m^2`, and so on until `k`, where there are `m^k` possible `Yk(tau)` sets. 
In practice, however, many of these sets are empty.

Let us look at an example:
```tla
VARIABLE 
  \* @type: Int;
  x

A1 == /\ x > 4
      /\ x' = x - 1

A2 == /\ x < 7
      /\ x' = x + 1

A3 == x' = x

A4 == /\ x = 1
      /\ x' = 10

Init == x \in 1..10
Next == \/ A1
        \/ A2
        \/ A3
        \/ A4
```

The `->` predicate can be decomposed into:
```
t1(s1,s2) = s1.x > 4 /\ s2.x = s1.x - 1
t2(s1,s2) = s1.x < 7 /\ s2.x = s1.x + 1
t3(s1,s2) = s2.x = s1.x
t4(s1,s2) = s1.x = 1 /\ s2.x = 10
```

Suppose we fix the length of the trace `k = 2`.
Without considering the decomposition, the symbolic trace is equal to 
```
X0 = 1..10, X1 = 1..10, X2 = 1..10
```

Under the decomposition, we have `m^k = 4^2 = 16` candidates for `tau`. Let us look at `tau1`, for which `tau1(1) = 1, tau1(2) = 2`, representing an execution where the action `A1` is followed by the action `A2`.
If `Y0,Y1(tau1),Y2(tau1)` is a partial trace (i.e. one of the elements in the decomposition `D`), then:
  
  - `Y1(tau1) = { b \in X1 : \E a \in Y0(tau1): t{tau1(1)}(a,b)}` which means
  ```
  Y1(tau1) = { b \in 1..10 : \E a \in 1..10 : a > 4 /\ b = a - 1 }
           = 4..9
  ```

  - `Y2(tau1) = { b \in X2 : \E a \in Y1(tau1): t{tau1(2)}(a,b)}` which means
  ```
  Y2(tau1) = { b \in 1..10 : \E a \in 4..9 : a < 7 /\ b = a + 1 }
           = 5..7
  ```

so the partial trace, corresponding to the sequence of actions `Init,A1,A2` is 
```
1..10, 4..9, 5..7
```

In fact, we can draw a table, representing partial traces corresponding to sequences of actions:

| Sequence of actions (after `Init`) | Partial trace (without `Y0`) |
|---|---|
| A1, A1 | `4..9, 4..8` |
| A1, A2 | `4..9, 5..7` |
| A1, A3 | `4..9, 4..9` |
| A1, A4 | `4..9, {}` |
| A2, A1 | `2..7, 4..6` |
| A2, A2 | `2..7, 3..7` |
| A2, A3 | `2..7, 2..7` |
| A2, A4 | `2..7, {}` |
| A3, A1 | `1..10, 4..9` |
| A3, A2 | `1..10, 2..7` |
| A3, A3 | `1..10, 1..10` |
| A3, A4 | `1..10, {10}` |
| A4, A1 | `{10}, {9}` |
| A4, A2 | `{10}, {}` |
| A4, A3 | `{10}, {10}` |
| A4, A4 | `{10}, {}` |

Clearly, the elements in every column (representing the various `Yi(tau)`), add up to `Xi = 1..10`. Also noticeable is the fact that some actions disable others, represented by the fact that some `Y2(tau)` sets are empty. For example, the action `A2` disables `A4`, because after `A2`, `x` cannot hold the value `1`, which is a precondition for `A4`.

### Counterexamples in Apalache
Finally, we can interpret Apalache counterexamples in the context of the above definitions. Given an invariant `I`, a transition system `(S, S0, ->)` and an upper bound on executions `k`, Apalache first finds predicates `t1,...,tm` partitioning `->`. Then,
it encodes a symbolic trace `X0,...,Xk` and its decomposition `D`. A counterexample in Apalache defines an explicit trace `s0,s1,...,sl \in S` for `l <= k`, as well as a sequence `t{tau(1)}, ..., t{tau(l)}` (in the comments). The predicate sequence defines a (prefix of a) partial trace
`Y0(tau),...,Yl(tau)` and `s0,...,sl` are chosen such that `si \in Yi(tau)`.

Take the following specification and counterexample, for `k = 10`:
```tla
---------- MODULE test ----------

EXTENDS Integers

VARIABLE
  \* @type: Int;
  x

A == /\ x = 1
     /\ x' = x + 1
B == /\ x > 1
     /\ 

Init == x = 1
Next == \/ A
        \/ B
Inv == x < 3 

====================

---------------------------- MODULE counterexample ----------------------------

EXTENDS test

(* Constant initialization state *)
ConstInit == TRUE

(* Initial state *)
State0 == x = 1

(* Transition 0 to State1 *)
State1 == x = 2

(* Transition 1 to State2 *)
State2 == x = 3

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == x >= 3

================================================================================
```

We can see that, even though `k=10`, we found a violation in `l=2` steps.
Each `State{i}` represents one of `s0,...,sl`, by explicitly defining variable values in that state (e.g. `x = 1 /\ y = 2 /\ z = "A"`). 
The comment `(* Transition X to StateY *)` outlines which `t1,...,tm` was used to reach `s{i+1}` from `si` (0-indexed). 
The shape of `ti` can be found by looking at the file `OutTransition.tla`, and will be named `Next_si_i`.
In the above case, `Transition 0` refers to the one representing `A` and `Transition 1` refers to the one representing `B`. 
`InvariantViolation` is the negation of the invariant `Inv`, and it will hold in `State{l}` (in this case, `x < 3` does not hold in `State2`, where `x = 3`).


