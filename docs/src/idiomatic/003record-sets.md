# Idiom 15: Replace sets of mixed records with disjoint unions

Message sets are canonically modeled as sets of records with mixed types.
While the current type system supports this, in the future,
Apalache is likely going to change support for these kinds of sets and implement stricter type-checking.
See [this](https://github.com/informalsystems/apalache/issues/401) issue for a discussion.
This document aims to provide instructions for users to migrate their specs to maintain type compatibility
in the future (and improve the performance and robustness of current specs in the present).

## The common approach
Apalache allows mixed sets of records, by defining the type of the set to be `Set(r)`,
where `r` is the record type which contains all the fields, which are held by at least one set member.
For example:

```tla
{ [x: Int], [y: Str] }
```

would have the type `Set([x:Int,y:Str])`.
The only constraints Apalache imposes are that, if two set elements declared the same field name,
the types of the fields have to match.
Consequently, given
```tla
A == { [x: Int, z: Bool], [y: Str, z: Bool] }
B == { [x: Int, z: Bool], [y: Str, z: Int] }
```
`A` is considered well typed, and is assigned the type `Set([x:Int, y:Str, z:Bool])`,
whereas `B` is rejected by the type checker.

The treatment of record types was implemented in this fashion,
to maintain backward-compatibility with specifications of message-based algorithms,
which typically encoded different message types as records of the shape `[ type: Str, ... ]`,
where all messages shared a disambiguation filed (commonly named `type`),
the value of which described the category of the message.
Additional fields depended on the value of `type`.
The bellow snippet from [Paxos.tla][] demonstrates this convention:
```tla
\* The set of all possible messages 
Message ==      [type : {"1a"}, bal : Ballot]
           \union [type : {"1b"}, acc : Acceptor, bal : Ballot, 
                 mbal : Ballot \union {-1}, mval : Value \union {None}]
           \union [type : {"2a"}, bal : Ballot, val : Value]
           \union [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]
```

Ultimately, this approach both disagrees with our interpretation of the purpose of a type-system for TLA+,
as well as introduces unsoundness, in the sense that it makes it impossible, at the type-checking level,
to detect record-field access violations.
Consider the following:
```
\E m \in Message: m.type = "1a" /\ m.mbal = -1
```
As defined above, messages for which `m.type = "1a"` do not define a field named `mbal`,
however, the type of `Message` is `Set([type: Str, ..., mbal: Int, ...])`,
which means, that `m` is assumed to have an `mbal` field, typed `Int`.
Thus, this access error can only be caught much later in the model-checking process,
instead of at the level of static analysis provided by the type-checker. 

## The proposed changes
This section outlines a proposed migration strategy, to replace such sets in older specifications.
The convention presented in this section works with both the current version of Apalache,
as well as the next iteration of the type-checker, currently in development.

Suppose we use messages with types `t1,...,tn` in the specification and a message set variable `msgs`,
like in the snippet below:
```tla

VARIABLE 
  \* @type: Set( [ type: Str, x1: a1, ..., xn: an, ... ] );
  msgs

...

\* Assuming S1: Set(a1), ..., Sn: Set(an) 
\* @type: Set( [ type: Str, x1: a1, ..., xn: an, ... ] );
Message ==      [type : {"t1"}, x1: S1, ...]
           \union  ...
           \union [type : {"tn"}, xn: Sn, ...]
...

TypeOk: msgs \subseteq Message
```

We propose the following substitution: Instead of modeling the union of all messages as a single set,
we model their disjoint union explicitly, with a record, in the following way:

```tla
\* @type: [ int: Set([x: Int]), str: Set([y: Str]) ];
Messages == [ 
              t1: [x1: S1, ...],
              ...,
              tn: [xn: Sn, ...] 
            ]
```
This way, `Messages.t1` represents the set of all messages `m`,
for which `m.type` would have been equal to "t1" in the original implementation, that is, `[type: {"t1"}, x1: S1, ...]`.
For example, assume the original specification included
```tla
Messages == [type: {"t1"}, x: {1,2,3}] \union [type: {"t2"}, y:{"a","b","c"}]
```
that is, defined two types of messages: "t1", with an integer-valued field "x" and "t2" with a string-valued field "y".
The type of any `m \in Messages` would have been `[type: Str, x: Int, y: Str]` in the old approach.
The rewritten version would be:
```tla
Messages == [ t1: [x:{1,2,3}], t2: [y:{"a","b", "c"}] ]
```
If we took `m: [ t1: Set([x: Int]), t2: Set([y: Str]) ]`, `m`
would be a record pointing to two disjoint sets of messages (of categories "t1" and "t2" respectively).
Values in `m.t1` would be records with the type `[x: Int]` and values in `m.t2` would be records with the type `[y: Str]`. 

Note, however, that this approach also requires a change in the way messages are added to,
or read from, the "set" of all messages (`m` is a record representing a set, but not a set itself, in the new approach).
Previously, a message `m` would be added by writing:
```
msgs' = msgs \union {m}
```
regardless of whether `m.type = "t1"` or `m.type = "t2"`.
In the new approach, one must always specify which type of message is being added.
However, the type no longer needs to be a property of the message itself, i.e. the `type` field is made redundant.

To add a message `m` of the category `ti` one should write
```
msgs' = [ msgs EXCEPT !.ti = msgs.ti \union {m} ]
```

Similarly, reading/processing a message, which used to be done in the following way:
```tla
\E m \in msgs:
  /\ m.type = "ti"
  /\ A(m)
```
is replaced by
```
\E m \in msgs.ti: A(m)
```

## Example
Below, we demonstrate this process on a concrete specification:
The old approach:
```tla
{{#include ./MsgSetOld.tla::}}
```

The new approach:
```tla
{{#include ./MsgSetNew.tla::}}
```

Note that the new approach, in addition to being sound w.r.t. record types,
also typically results in a performance improvement,
since type-unification for record sets is generally expensive for the solver.

[Paxos.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/Paxos/Paxos.tla
