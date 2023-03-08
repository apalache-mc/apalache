# Context-based static analysis

This document is meant for Apalache developers, and aims to explain some of the intricacies of context-based static analyses such as the arena preconstruction outlined in ADR24.

## Preamble

Recall that every expression in Apalache's IR tree is annotated with a unique identifier (UID). This serves as a way to disambiguate syntactically equivalent (sub-)expressions in different parts of the specification:

```tla
f(x) == x + 1 // the "x" has UID u1
g(x) == x - 1 // the "x" has UID u2
```

For some analyses, it is sufficient to assign a value to every UID (or to a subset thereof). For instance, assignment analysis assigns a set of variables to every Boolean-connective node in the IR tree; the set of guaranteed assignments below that node.

## Contexts 

Sometimes, however, static analyses are concerned with _semantics_, rather than _syntax_. Consider the following expression:

```tla
\E v \in  S: x' = v - 20
```

The subexpression `v - 20` has ambiguous arithmetic properties. For example, it cannot be deduced, without considering exactly which element from `S` was chosen, whether this expression can be negative; that property depends on the _context_ in which this expression is evaluated, not on syntax itself.

For the purpose of this document, we define a `T`-context, as a mapping from TLA+ identifiers (e.g. variable/parameter names) to values of type `T`.
In particular, a cell context assigns arena cells to identifiers.

We denote (cell) contexts using the following notation:
```
mu = { v -> c_1, y -> c_2 }
```

meaning the context `mu` maps the identifier `v` to the cell `c_1`, and the identifier `y` to the cell `c_2`. We only care about finite-domained contexts, so w.l.o.g. we are going to assume all contexts described in this document have finite domains.

## Cell-context based arena analysis

Consider the following goal: We want to, without discharging SMT constraints, precompute an arena, such that the model checking pass can apply a sequence of (modified) rewriting rules, which only ever read from the arena.

This requires us to:
  1. Prepare a cell of the correct type, for every expression, which needs to be evaluated during the rewriting process (this includes generated expressions, more on this later)
  2. Provide a way of accessing the required cells from within the rewriting rules

Looking at (2), one would naturally want to map each subexpression (via UID) to an arena cell, which represents the outcome of fully rewriting the subexpression (recall, the rewriting of a TLA expression, as described in the OOPSLA paper, terminates when the entire expression has been rewritten to a single cell, expanding the arena and generating SMT constraints in the process).

However, this naive approach _does not work_. There are multiple rules which run into the same issue, but we can focus on one in particular: `EXISTS`.

The rule states the following: Given an expression `\E x \in c_S: p`, where `c_S` is a cell, for which the arena contains has-edges to `c_1,...,c_n`, the expression rewrites to the nondeterministic disjunction of `p[c_1/x], ..., p[c_n/x]` (which rewrites further by other rewriting rules, eventually terminating in a single cell).

The problem is that expressions `p[c_1/x], ..., p[c_n/x]` are ephemeral. 
They are syntactic derivatives of `p`, but we cannot use the same (one) cell, which the naive mapping would assign to `p`. 
We also cannot pre-assign them cells, because the moment these fresh expressions are created as part of the rewriting rule, they get assigned _unique_ identifiers.

We could potentially assign a _tuple_ (or _list_) of cells to `p`, the length of which would equal the size of the has-relation of `S` (= `m`), but that approach is brittle. 
It also becomes incredibly difficult to track with quantifier nesting.
For instance, if we had
```tla
\E x_1 \in S: \E x_2 \in S: ... \E x_n \in S: p
```

we would effectively be assigning `m`-by-`n` matrices to `p`. It is well known that the `m`-by-`n` matrix space is isomorphic to the `mn` tuple space, so we could pack those neatly in a single tuple (or list), but deciphering this becomes impractical, and accidentally accessing the wrong index is extremely easy.

We opt instead, to capture such bound variables in a _cell-context_. Observing the sub-expression `p`, with UID `u` in the above expression, we can assign a cell to every _context_ `mu = { x_1 -> c_1, ..., x_n -> c_n }`. This effectively gives us a global mapping `(u, mu) |-> c`, where each UID is assigned a unique cell _in a given cell-context_.

## Accessing the right context

A potential optimization issue arises with the above approach. Consider the expression
```tla
\E x \in S:
  \E y \in S:
    \E z \in S: 
      r > x + y + z \* we call this subexpresison e, with UID u
```

wherein `r` is a variable or parameter, defined outside the triple `\E`. If 
`S` has `n` arena has-edges, then there are `n^3` contexts in which to evaluate e, so we _need_ map entries `(u, mu_1),...,(u, mu_n^3)`. However, if we look at `r`, the subexpression of `e`, storing entries for `(_, mu_1),...,(_, mu_n^3)` would be redundant, and potentially expensive, since all those entries would necessarily point to the same cell; `r` is defined outside of this quantifier context, so any value it takes inside of the quantifiers is independent of the bound variables.

This brings us to the following realization: we don't need to store cells for every pair of UID and cell-context, only for those, where the cell context domain is exactly the set of free variables appearing in the expression referenced by the UID. 








