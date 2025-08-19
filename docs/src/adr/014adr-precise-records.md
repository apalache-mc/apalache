# ADR-014: Precise type inference for records and variants

| authors                                | last revised    |
| -------------------------------------- | --------------: |
| Igor Konnov                            | 2021-12-12      |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## 1. Summary

This ADR extends
[ADR-002](https://apalache-mc.org/docs/adr/002adr-types.html) on
types and type annotations.

Virtually every user of Snowcat has faced the issue of record type checking
being imprecise. Some people call it "unsound", though soundness depends on the
type system. This is due to our decision to support the variant pattern that
can be found in untyped TLA+ specifications. In this ADR, we are proposing a
plan of action for introducing precise type inference for records and variants
(discriminated unions) in the type checker. This would deliver the most asked
feature. On the downside, we would have to:

1. Increase the complexity of the type checker.

1. Slightly update the rewriting rules in the model checker.

1. Require the users to modify their specs to use the variant operators.

As much as possible, we have tried to make the type annotations non-intrusive and compatible with
TLC. After precisely specifying the requirements for the variant
type, we have found that it would be impossible to do sound type checking
without introducing additional operators.

We believe that the benefits outweigh the downsides in the long run. Moreover,
it will improve user experience, as this is the most requested feature.

## 2. Context

As discussed in [ADR002][], the type checker is not checking the record types
precisely. Consider the following operator:

```tla
Foo ==
  LET S == {[ type |-> "A", a |-> 1], [ type |-> "B", b |-> 2 ]} IN
  \E m \in S:
    m.a > m.b
```

The type checker assigns the type `Set([type: Str, a: Int, b: Int])` to `S`. As
a result, one can write the expression `m.a > m.b`, which does not make a lot
of sense. This may lead to unexpected results in a large specification. In the
above example, the model checker would just produce some values for `m.a` or
`m.b`, which will probably result in a spurious counterexample.

Further, multiple related issues and potential solutions were underlined in
[#401][] and [#789][].

There are two main patterns of record use in TLA+:

1. **Plain records**. A record with a fixed number of fields is passed around.

1. **Variants**. Records of various shapes are collected in a single
   set and passed around. The precise record shape is controlled with a special
   field (discriminator), which is usually called `type` in TLA+ specs.

### 2.1. Untyped plain records

When it comes to records, it is clear that users expect the type checker to complain about missing record fields. Indeed, it is very
easy to introduce a spurious record field by mistyping the field name. It
happened to all of us.

Interestingly, plain records are used less often than variants.
Perhaps, if records are required, the specification is quite complex already,
so it would also need variants.

Occurences in [tlaplus-examples](https://github.com/tlaplus/Examples):

 - [ACP_NB](https://members.loria.fr/SMerz/talks/argentina2005/Charpentier/charpov/Teaching/CS-986/TLC/ACP_NB.tla)
 - [c1cs](https://github.com/tlaplus/Examples/blob/master/specifications/c1cs/c1cs.tla)
 - [EnvironmentController](https://github.com/tlaplus/Examples/blob/master/specifications/detector_chan96/EnvironmentController.tla)
 - [LamportMutex](https://github.com/tlaplus/Examples/blob/master/specifications/lamport_mutex/LamportMutex.tla)
 - [voldchain](https://github.com/muratdem/PlusCal-examples/blob/master/VoldemortKV/voldchain.tla)
 - [TPaxos](https://github.com/Starydark/Tencent-Paxos-TLA/blob/master/TPaxos.tla)
 - [Echo](https://github.com/tlaplus/Examples/blob/master/specifications/echo/Echo.tla)

[LamportMutex](https://github.com/tlaplus/Examples/blob/master/specifications/lamport_mutex/LamportMutex.tla)
is an interesting borderline case, in which the spec uses the variant pattern,
but it could be typed with a single record type. Here are the interesting pieces
in this spec:

```tla
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage == [type |-> "ack", clock |-> 0]
RelMessage == [type |-> "rel", clock |-> 0]

Message == {AckMessage, RelMessage} \union {ReqMessage(c) : c \in Clock}

...
Broadcast(s, m) ==
  [r \in Proc |-> IF s=r THEN network[s][r] ELSE Append(network[s][r], m)]
...
Request(p) ==
  ...
  /\ network' = [network EXCEPT ![p] = Broadcast(p, ReqMessage(clock[p]))]
  ...
```

Although, every message record is accompanied with the field `type`, all
records have the same shape, namely, they have two fields: A string field
`type` and an integer field `clock`.

### 2.2. Untyped variants

Most of the benchmarks stem from the Paxos specification. They all follow the
same pattern. Messages are represented with records of various shapes. Every
record carries the field `type` that characterizes the record shape. For instance,
here is how records are used in Paxos:

```tla
Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot, 
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]
...
Send(m) == msgs' = msgs \cup {m}
...
Phase1b(a) == /\ \E m \in msgs : 
                  /\ m.type = "1a"
                  /\ m.bal > maxBal[a]
                  ...
                  /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, 
                            mbal |-> maxVBal[a], mval |-> maxVal[a]])
              ...
```           

Occurences in [tlaplus-examples](https://github.com/tlaplus/Examples):

 - [Paxos](https://github.com/tlaplus/Examples/blob/master/specifications/Paxos/Paxos.tla)
 - [802.16](https://github.com/tlaplus/Examples/tree/master/specifications/802.16)
 - [byihive](https://github.com/byisystems/byihive/blob/master/specifications/tla%2B/VoucherIssue.tla)
 - [CASPaxos](https://github.com/tbg/caspaxos-tla/blob/master/CASPaxos.tla)
 - [cbc_max](https://github.com/tlaplus/Examples/blob/master/specifications/cbc_max/cbc_max.tla)
 - [EgalitarianPaxos](https://github.com/efficient/epaxos/blob/master/tla%2B/EgalitarianPaxos.tla)
 - [FPaxos](https://github.com/fpaxos/fpaxos-tlaplus/blob/master/FPaxos.tla)
 - [raft](https://github.com/ongardie/raft.tla/blob/master/raft.tla)
 - [SnapshotIsolation](https://github.com/sanjosh/tlaplus/blob/master/amazon/serializableSnapshotIsolation.tla)
 - [PaxosCommit](https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/PaxosCommit.tla)


More advanced code patterns over variants can be found in [Raft][]:

```tla
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)
    ...
Next ==
    ...
           \/ \E m \in DOMAIN messages : Receive(m)
           \/ \E m \in DOMAIN messages : DuplicateMessage(m)
           \/ \E m \in DOMAIN messages : DropMessage(m)
    ...
```

### 3. Other issues

As can be seen from the Paxos example, we should take care of sets of
records that are used as sets of variants:

```tla
Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot, 
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]
```           

## 4. Options

There are several solutions to the issue of precise record typing.

### 4.1. Support only plain records

In this case, we would only allow to mix records that have exactly the same
shape. As a result, when we use variants, we would have to add extra
fields to all of them. This solution is not very different from the current
implementation of record type checking, though it would allow us to quickly
detect spelling errors.

**Blocker.** This does not look like a real solution, as it would immediately
render the existing examples invalid. Moreover, they would be no obvious way to
repair these examples.

### 4.2. Support plain records and variants, but no row typing

In this scenario, the type checker would issue an error, if a record expression
accesses a field that is outside of its type:

```tla
FieldAccess ==
  LET m == [ a |-> 2, b |-> "B" ] IN
  /\ m.a > 1        \* type OK
  /\ m.b = "B"      \* type OK
  /\ m.c = { 1, 2 } \* should flag a type error
```

Moreover, the following example would require a type annotation:

```tla
RowAccess(m) ==
    m.a > 0         \* should flag a type error
```

In the above example, the type checker would not be able to infer the type of
`m` and would require an explicit type annotation:


```tla
\* @type: [ a: Int, b: Str ];
RowAccessAnnotated(m) ==
    m.a > 0         \* should not flag a type error
```

**Blocker.** It is not clear to me, what type we would assign to the record
access operator. Although the type of `m` in `FieldAccess` is obvious to a
human reader, as it simply requires us to do the top-to-the-bottom type
propagation, Snowcat constructs a set of equality constraints that are solved
by unification. This approach requires that we capture the record access
operator `.` as an equality over type variables and types.

### 4.3. Support plain records and variants, including row typing

This solution is inspired by the approach outlined by [Leijen05][], but is much more limited. The following features discussed in [Leijen05][] are neither needed needed nor supported:

- extension for records
- extension for variants
- record restriction
- scoped labels

Our use is limited to a few special cases that give support for subtyping and incremental inference of anonymous record types, in which we cannot know the full set of fields up front. 

## 5. Solution

In the following, we present row types as type terms. We discuss the
user-facing syntax of the type system later in the text.

### 5.1. Plain records

By using [Row types][], we should be able to infer a polymorphic record type for  `m` in the unannotated
`RowAccess` operator:

```
Rec(RowCons("a", Int, z))
```

In this example, `RowCons("a", Int, z)` indicates a row indicating that the type of the record enclosing it
has the field `a` of type `Int`. On top of that, this row
extends a parametric type `z`, which either contains a non-empty sequence of
rows, or is an empty sequence, that is, `RowNil`. Importantly, `RowCons` is
wrapped with the term `Rec`, so no additional fields can be added to the type.

The example `FieldAccess` contains a record constructor
`[ a |-> 2, b |-> "B" ]`. We can write a general type inference rule for it:

```
e_1: t_1, ..., e_n: t_n
-------------------------------- [rec]
[ f_1 |-> e_1, ..., f_n |-> e_n]:
  Rec(
    RowCons(f_1, t_1,
      RowCons(f_2, t_2,
        ...
          RowCons(f_n, t_n, RowNil)
      ...)
    )
  )
```

In `FieldAccess`, we use row types to construct a series of type equations
(over free type variables `k`, ..., `q`):

```
// from LET m == [ a |-> 2, b |-> "B" ] IN
m_type = Rec("a", Int, RowCons("b", Str, RowNil))
// from m.a > 1
m_type = Rec(RowCons("a", k, l))
k = Int
// from m.b = "B"
m_type = Rec(RowCons("b", m, n))
m = Str
// from m.c = { 1, 2 }
m_type = Rec(RowCons("c", p, q))
p = Set(Int)
```

To solve the above equations, one has to apply unification rules. Precise
unification rules for rows are given in the paper by [Leijen05][]. Importantly,
their unification rules allow `RowCons(f1, t1, RowCons(f2, t2, r3))` to be
unified with `RowCons(f2, t2, RowCons(f1, t1, r3))`. Hence, fields may bubble
up to the head, and it should be possible to isolate a single field and assign
the rest to a type variable. By partially solving the above equation, we would
arrive at contradiction. This supports our intuition that the operator
`FieldAccess` is ill-typed.

Hence, we formulate the type inference rule for record access in our type
system as follows:

```
r: Rec(RowCons("f", t_1, t_2))
-------------------------------- [rec_acc]
r.f: t_1
```

Note that the above rule can be rewritten into a series of equalities over
types variables and type terms, which is how this would be implemented in the
type checker.

If we only had to deal with records, that would be a complete solution.
Unfortunately, variants introduce additional complexity.

### 5.2. Variants

**Example 5.2.1.** Now we have to figure out how to deal with TLA+ expressions
like:

```tla
  { [ tag |-> "1a", bal |-> 3 ], [ tag |-> "2a", bal |-> 4, val |-> 0 ] }
```

Obviously, we cannot fit both of the records into a single plain record type,
provided that we want to precisely track the fields that are present in a
record. So the type checker should report a type error, if we only implement
type inference for the case explained in Section 5.1. To support this important
pattern, we introduce variants. They are similar to [unions in
TypeScript](https://www.typescriptlang.org/docs/handbook/2/everyday-types.html#union-types).
In contrast to TypeScript, we fix one field to designate the record type in a
variant. Also, we are using the word "variant", to avoid any confusion
with the TLA+ operators `UNION` and `\union`.

We reserve the field name `tag` for the record discriminator.

**Variant constructor.** We introduce a special TLA+ operator `Variant`
that extracts the tag from a record and wraps the record into a variant.
We need this operator to distinguish between plain records and records that
belong to a variant. The operator `Variant` is defined in TLA+ as follows:

```tla
  Variant(r) ==
    \* fallback untyped implementation
    r
```

This operator does not change its argument, but it provides the type checker
with a hint that the record should be treated as a member of a variant.

Consider the record constructor of `n+1` fields, one of them being the field
`"tag"`:

```tla
  [ tag |-> "<TAG>", f_1 |-> e_1, ..., f_n |-> e_n ]
```

Here, `"<TAG>"` stands for a string literal such as `"1a"` or `"2a"`. The
general rule for `Variant([ tag |-> "<TAG>", f_1 |-> e_1, ..., f_n |-> e_n ])`
looks as follows:

```
e_1: t_1, ..., e_n: t_n
z is a fresh type variable
------------------------------------------------------------ [variant]
Variant([ tag |-> "<TAG>", f_1 |-> e_1, ..., f_n |-> e_n ]):
  Variant(
    RowCons("<TAG>",
      Rec(
        RowCons("tag", Str,
          RowCons(f_1, t_1,
            ...
              RowNil)...)
      ),
      z
    )
  )
```

According to the rule `[variant]`, the operator `Variant` wraps a record
constructor that contains a string literal for the field `tag`. The variant
contains the record that was passed in the constructor, whereas the other
alternatives of the variant are captured with a fresh type variable `z`, which must
be a row.

Importantly, we use rows at two levels:

1. To construct a single record, whose shape is defined precisely.

1. To construct a variant, whose only record is known at the time,
   while the rest is captured with the type variable `z`.

Going back to **Example 5.2.1**, the set constructor would produce a set of
equalities:

```
  a = Set(b)
  a = Set(d)
  b = Variant(RowCons("1a",
                Rec(RowCons("tag", Str, RowCons("bal", Int, RowNil))),
              c))
  d = Variant(RowCons("2a",
                Rec(RowCons("tag", Str,
                  RowCons("bal", Int,
                    RowCons("val", Int, RowNil)))),
              e))
```

By solving these equalities with unification, we will arrive at the following
variant:

```
  Set(Variant(RowCons(
               "1a",
               Rec(RowCons("tag", Str, RowCons("bal", Int, RowNil))),
               RowCons(
                 "2a",
                 Rec(RowCons("tag", Str,
                       RowCons("bal", Int,
                         RowCons("val", Int, RowNil)))),
                 t
     ))))
```

Note that we still do not know the precise shape of the variant, as it
closes with the type variable `t`. This is actually what we expect, as the set
may be combined with records of other shapes. Normally, the final shape of a
variant propagates via state variables of the TLA+ specification.

**Type annotations for variants.** Snowcat requires that all state variables
are annotated. What shall we write for variants?  We introduce the common type
notation for variants that separates records with a pipe, that is, `|`. For
instance, consider the following variable declaration in a TLA+ specification:

```tla
VARIABLES
  \* @type: Set([ tag: "1a", bal: Int ] | [ tag: "2a", bal: Int, val: Int ]);
  msgs
```

Note that even though the syntax of individual elements of a variant is very
similar to that of a record, there is small difference: The tag field is not
declared as a string type, but carries the values of the tag itself.

As variants can grow large very quick, it is more convenient to introduce them
via a type alias. For instance:

```tla
VARIABLES
  (*
    @typeAlias: MESSAGE =
       [ tag: "1a", bal: Int ]
     | [ tag: "2a", bal: Int, val: Int ]);
    @type: Set(MESSAGE);
   *)  
  msgs
```


**Filter a set of variants.** As we have seen, the following pattern
is quite common in TLA+ specifications, e.g., it is met in Paxos:

```tla
  \E m \in msgs:
    /\ m.type = "1a"
    ...
  LET Q1b == { m \in msgs : m.type = "1b" /\ ... }
```

We introduce the operator `FilterByTag` that is a type-safe version of this
pattern:

```tla
FilterByTag(Set, tag) == { e \in Set: e.tag = tag }
```

We introduce a special type inference rule for `FilterByTag`:

```
set: Set(Variant(RowCons("<TAG>", r, z)))
------------------------------------------- [variant_filter]
FilterByTag(set, "<TAG>"): Set(r)
```

Importantly, `FilterByTag` returns a set of records that carry the tag `<TAG>`,
so we can access record fields of every individual record in the set.

**Match by tag.** In rare cases, we do not have a set to filter. For instance,
we could have a sequence of log messages:

```tla
VARIABLE
  \* @type: Seq([ tag: "EventA", val: Int ] | [ tag: "EventB", src: Str ]);
  log
```

In this case, we would not be able to easily use `FilterByTag`. Of course, we
could wrap a variant into a singleton set and then apply `FilterByTag` to it
and `CHOOSE` on top of it. However, this looks clunky and does not guarantee
type safety. A much simpler solution is to introduce another special operator:

```tla
MatchTag(variant, tag, ThenOper(_), ElseOper(_)) ==
  \* fallback untyped implementation
  IF variant.tag = tag
  THEN ThenOper(variant)
  ELSE ElseOper(variant)
```

The idea of `MatchTag` is that it passes the extracted record to `ThenOper`,
when its tag value matches `tag`; otherwise, it passes the reduced variant to
`ElseOper`. This is precisely captured by the inference rule:

```
variant: Variant(RowCons("<TAG>", r, t))
ThenOper: r => z
ElseOper: Variant(t) => z
------------------------------------------------ [variant_match]
MatchTag(variant, "<TAG>", ThenOper, ElseOper):
  (Variant(RowCons("<TAG>", r, t)),
   Str,
   r => z,
   Variant(t) => z
  ) => z
```

The above rule looks menacing. Here is an example of matching a record
in the above example with the variable `log`:

```tla
IsDefined(eventAOrB) ==
  LET ElseB(onlyB) ==
    MatchTag(onlyB, "EventB", LAMBDA b: b.src /= "", LAMBDA elseValue: FALSE)
  IN  
  MatchTag(event, "EventA", LAMBDA a: a.val /= -1, ElseB)
```

The operator `ElseB` looks redundant, as we know that `onlyB` is a singleton
variant. To this end, we introduce the operator `MatchOnly`:

```tla
MatchOnly(variant, ThenOper(_)) ==
  \* fallback untyped implementation
  ThenOper(variant)
```

For completeness, we give the inference rule for `MatchOnly`:

```
variant: Variant(RowCons("<TAG>", r, RowNil))
ThenOper: r => z
------------------------------------------------ [variant_match_only]
MatchOnly(variant, ThenOper):
  (Variant(RowCons("<TAG>", r, RowNil)),
   r => z
  ) => z
```

It looks like the solution with `MatchTag` and `MatchOnly` introduce a lot of
boilerplate. However, this is probably the best solution that we can have,
unless we can extend the grammar of TLA+.

### 5.3. Changes in the model checker

Having precise types for variants, we have two options:

 1. Keep the current encoding, that is, a variant is encoded as a super-record
 that contains all possible fields of the member records. The type checker
 will guarantee that we do not access the fields of the super-record that are
 not present in the actual record type.

 1. Implement the
 [suggestion by Shon Feder](https://github.com/apalache-mc/apalache/discussions/789#discussioncomment-1592118).

Although Option 2 looks nicer, we prefer keeping Option 1. The reason is that
the current implementation introduces the minimal number of constraints
by mashing all possible fields into a super-record. The alternative solution
(option 2) would introduce additional constraints, when the spec requires us
to extract an element from a set.

Recall the example with a set of messages:

```tla
VARIABLES
  (*
    @typeAlias: MESSAGE =
       [ tag: "1a", bal: Int ]
     | [ tag: "2a", bal: Int, val: Int ]);
    @type: Set(MESSAGE);
   *)  
  msgs
```  

Consider an existential quantifier over the variable `msgs`:

```tla
Next ==
  \E m \in msgs:
    P
```

In the current encoding, `m` is a super-record that contains three fields:
`tag`, `bal`, and `val`, even if some of these fields are not required by the
actual type of `m`. In the alternative encoding, `m` is a tuple `tup`,
which equals to one of the following tuples, depending on the value of the
field `m.tag`:

```
tup = IF m.tag = "1a"
      THEN << { [ tag |-> "1a", bal |-> b ] }, {} >>
      ELSE << {}, [ tag |-> "2a", bal |-> b, val |-> v ] }, {} >>
```

Since it is impossible to statically compute the actual type of `m`, the
rewriting rules would have to replicate the structure of both elements of the
tuple `tup`. This would lead to a blow-up in the number of constraints.

### 5.4. Additional requirements

Given the decisions in Section 5.3, we additionally require that all records in
a variant type have compatible field types. In more detail, if a variant type
contains two record types `[ tag: "A", value: a, ... ]` and `[ tag: "B", value:
b, ...]`, then the types `a` and `b` must be unifiable.  In practice, this
often implies that `a` and `b` are simply the same type.

### 5.5. The Variants module

We introduce a new module that is called `Variants.tla`. It contains the
operators `Variant`, `FilterByTag`, `MatchTag`, and `MatchOnly`. This module
will be distributed with Apalache. As is custom in the TLA+ community, the
users should be also able to copy `Variants.tla` next to their specification.

## 6. Consequences

This will be a relatively big change in the types and the type checker.
Additionally, it would render many existing specifications ill-typed, as the
proposed solution imposes a stricter typing discipline. On the positive, the
proposed solution is backwards-compatible with TLC, as we are proposing the
default untyped implementation for the operators.



[ADR002]: https://apalache-mc.org/docs/adr/002adr-types.html
[#401]: https://github.com/apalache-mc/apalache/issues/401
[#789]: https://github.com/apalache-mc/apalache/discussions/789
[Raft]: https://github.com/ongardie/raft.tla/blob/master/raft.tla
[Leijen05]: https://www.microsoft.com/en-us/research/publication/extensible-records-with-scoped-labels
[Row types]: https://www.microsoft.com/en-us/research/publication/extensible-records-with-scoped-labels/
