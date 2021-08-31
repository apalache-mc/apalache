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


[Issue 711]: https://github.com/informalsystems/apalache/issues/711
[Issue 712]: https://github.com/informalsystems/apalache/issues/712
[Issue 401]: https://github.com/informalsystems/apalache/issues/401
