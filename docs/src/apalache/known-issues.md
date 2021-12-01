# Known issues

This page collects known issues that were reported by the users.

## Deadlock detection

Deadlock detection is imprecise. It may report false negatives, see [Issue
711][].

**Affected versions:** <= 0.15.x

**Planned fix:** [Issue 712][]

## Updating records with excess fields

Given a record with a type declaration specifying `n` fields, if that record is
given more than `n` fields and the specification includes an `EXCEPT` expression
that updates the record, Apalache may be unable to check the specification.

In the following example, the variable `m` is given the type of a record with
`1` field (namely `a`), but it is then assigned to a record with `2` fields
(namely `a` and `foo`).

```tla
VARIABLE
  \* @type: [a: Int];
  m

Init == m = [a |-> 0, foo |-> TRUE]

Next ==
   \/ m' = m
   \/ m' = [m EXCEPT !.a = 0]
```

Given the current (unsound) typing discipline Apalache uses for records, this
specification is not considered incorrectly typed. However, due to the update
using `EXCEPT` in the `Next` operator, the specification cannot be checked.

**Affected versions:** <= 0.15.x

**Planned fix:** [Issue 401][]

### Workaround

Add the `foo` field to the variable's type signature:

```tla
VARIABLE
  \* @type: [a: Int, foo: Bool];
  m

Init == m = [a |-> 0, foo |-> TRUE]

Next ==
   \/ m' = m
   \/ m' = [m EXCEPT !.a = 0]
```

## Integer ranges with non-constant bounds

When using an integer range `a..b`, where `a` or `b` aren't constant (or cannot be simplified to a constant), the current encoding fails (see [Issue 425][]):

```tla
---------- MODULE Example ----------

EXTENDS Integers

VARIABLE 
  \* @type: Int;
  x

\* @type: (Int) => Set(Int);
1to(n) == 1..n

Init == x = 1

Next == x' = x + 1

Inv == 1 \in { m: a \in 1to(x) }
====================
```

**Affected versions:** All

**Planned fix:** Not in the near future

### Workaround

Pick constant bounds `Nmin` and `Nmax`, such that `Nmin <= a <= b <= Nmax`, then use

```tla
range(a,b) == { x \in Nmin..Nmax: a <= x /\ x <= b }
```

instead of `a..b`.

## Using Seq(S)

The operator `Seq(S)` produces an infinite set of unbounded sequences. Hence, Apalache is not able to do anything about
this set. Consider the following snippet:

```tla
  \E s \in Seq({ 1, 2, 3 }):
     seq' = s
```

**Affected versions:** All

**Planned fix:** Not in the near future

### Workaround

If you know an upper bound on the length of sequences you need, which is often the case when checking one model, you can
work around this issue by using
[Apalache.Gen](https://github.com/informalsystems/apalache/blob/0bf827c521d3992f39e085cc98ff114bfa0b1721/src/tla/Apalache.tla#L31-L39):

```tla
EXTENDS Apalache
...
  LET s == Gen(10) IN
  /\ \A i \in DOMAIN s:
      s[i] \in { 1, 2, 3 }
  /\ seq' = s
```

In the above example, we instruct Apalache to introduce an unrestricted sequence that contains up to 10 elements; this
is done with `Gen`. We further restrict the sequence to contain the elements of `{ 1, 2, 3 }`.

However, note that our workaround only works for bounded sequences, whereas
`Seq({ 1, 2, 3 })` is the set of all sequences whose elements come from `{ 1, 2, 3 }`.

[Issue 425]: https://github.com/informalsystems/apalache/issues/425

[Issue 711]: https://github.com/informalsystems/apalache/issues/711

[Issue 712]: https://github.com/informalsystems/apalache/issues/712

[Issue 401]: https://github.com/informalsystems/apalache/issues/401
