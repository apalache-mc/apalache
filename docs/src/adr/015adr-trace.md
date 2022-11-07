# ADR-015: Informal Trace Format in JSON

| authors                                | proposed by                   | last revised    |
| -------------------------------------- | ----------------------------  | --------------: |
| Igor Konnov                            | Vitor Enes, Andrey Kupriyanov | 2022-11-03      |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

We propose a simple format for counterexamples (traces) in [JSON][]. Although
Apalache already supports serialization to [JSON][] in [ADR005][], it is a
general serialization format for all the constructs of TLA+ that are supported
by Apalache. This makes tool integration harder. It also make it hard to
communicate counterexamples to engineers who are not familiar with TLA+. This
ADR-015 contains a very simple format that does not require any knowledge of
TLA+ and can be easily integrated into other tools.

## Context

A TLA+ execution (called a behavior in TLA+) is a very powerful concept. It can
represent virtually any execution of a state machine, including sequential
programs, concurrent programs, and distributed systems. Counterexamples that
are produced by TLC and Apalache are just executions of a TLA+ state machine.
These counterexamples have two shapes:

 1. A *finite execution*, that is, a sequence of states.

 1. A *lasso execution*, that is, a finite sequence of states (prefix) followed
 by an infinitely repeated sequence of states (loop). Any infinite execution of
 a *finite-state system* can be represented by a lasso.  (In general, executions
 of infinite-state systems cannot be represented by lassos.)

Although the concept of an execution in TLA+ is quite simple, it builds upon
the vocabulary of TLA+. Moreover, TLA+ counterexamples are using the expression
language of TLA+.

To illustrate the problem, consider a very simple TLA+ specification of the
MissionariesAndCannibals puzzle (specified by Leslie Lamport). We use a typed
version of this specification, see [MissionariesAndCannibalsTyped][]. Consider
the following instance of the specification:

```tla
------------------- MODULE MC_MissionariesAndCannibalsTyped -----------------    
Missionaries == { "m1_OF_PERSON", "m2_OF_PERSON" }
Cannibals == { "c1_OF_PERSON", "c2_OF_PERSON" }

VARIABLES
    \* @type: Str;
    bank_of_boat,
    \* @type: Str -> Set(PERSON);
    who_is_on_bank

INSTANCE MissionariesAndCannibalsTyped

NoSolution ==
    who_is_on_bank["E"] /= {}
=============================================================================
```

By checking the invariant `NoSolution`, we obtain the following counterexample
in TLA+:

```tla
---------------------------- MODULE counterexample ----------------------------

EXTENDS MC_MissionariesAndCannibalsTyped

(* Constant initialization state *)
ConstInit == TRUE

(* Initial state *)
State0 ==
  bank_of_boat = "E"
    /\ who_is_on_bank
      = "E"
          :> { "c1_OF_PERSON", "c2_OF_PERSON", "m1_OF_PERSON", "m2_OF_PERSON" }
        @@ "W" :> {}

(* Transition 0 to State1 *)
State1 ==
  bank_of_boat = "W"
    /\ who_is_on_bank
      = "E" :> { "c1_OF_PERSON", "m1_OF_PERSON" }
        @@ "W" :> { "c2_OF_PERSON", "m2_OF_PERSON" }

(* Transition 0 to State2 *)
State2 ==
  bank_of_boat = "E"
    /\ who_is_on_bank
      = "E" :> { "c1_OF_PERSON", "m1_OF_PERSON", "m2_OF_PERSON" }
        @@ "W" :> {"c2_OF_PERSON"}

(* Transition 0 to State3 *)
State3 ==
  bank_of_boat = "W"
    /\ who_is_on_bank
      = "E" :> {"c1_OF_PERSON"}
        @@ "W" :> { "c2_OF_PERSON", "m1_OF_PERSON", "m2_OF_PERSON" }

(* Transition 0 to State4 *)
State4 ==
  bank_of_boat = "E"
    /\ who_is_on_bank
      = "E" :> { "c1_OF_PERSON", "c2_OF_PERSON" }
        @@ "W" :> { "m1_OF_PERSON", "m2_OF_PERSON" }

(* Transition 0 to State5 *)
State5 ==
  bank_of_boat = "W"
    /\ who_is_on_bank
      = "E" :> {}
        @@ "W"
          :> { "c1_OF_PERSON", "c2_OF_PERSON", "m1_OF_PERSON", "m2_OF_PERSON" }

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == who_is_on_bank["E"] = {}

================================================================================
(* Created by Apalache on Wed Dec 22 09:18:50 CET 2021 *)
(* https://github.com/informalsystems/apalache *)
```

The above counterexample looks very simple and natural, if the reader knows
TLA+. In our experience, these examples look alien to engineers, who are not
familiar with TLA+. It is unfortunate, since the counterexamples have a very
simple shape:

 1. They are simply sequences of states.

 1. Every state is a mapping from variable names to expressions that do not
 refer to other variables.

 1. The expressions are using a very small subset of TLA operators:

   1. Integer and string literals.

   1. Set constructor, sequence/tuple constructor, record constructor.

   1. TLC operators over functions: `:>` and `@@`.

In hindsight, the above expressions are not very far from the JSON format.
As many engineers know [JSON][], it seems natural to write these counterexamples
in JSON.

## Options

 1. Use the TLA+ format:

    - Pros:

      - easy to understand, if you know TLA+.
      - it looks amazing in PDF.

    - Cons:

      - quite hard to understand, if you don't know TLA+.
      - quite hard to parse automatically.

 1. Use the JSON serialization as in [ADR005][]:

    - Pros:

      - easy to parse automatically.

    - Cons:

      - almost impossible to read.
      - too detailed and too verbose.
      - requires the knowledge of Apalache IR and of TLA+.

 1. Use the Informal Trace Format, which is proposed in this ADR:

    - Pros:

      - almost no introduction is required to read the traces.
      - relatively compact.
      - easy to parse automatically.
      - uses the idioms that are understood by the engineers.
      - not bound to TLA+.

    - Cons:

      - consistency of the format is in conflict with the ease of writing.

## Solution

In this ADR, we propose a very simple format that represents executions of
state machines that follows the concepts of TLA+ and yet avoids complexity of
TLA+. It is so simple that we call it *"Informal Trace Format"* (ITF).
(Obviously, it is formal enough to be machine-readable).  By convention, the
files in this format should end with the extension `.itf.json`.

### The ITF Format

**Trace object**. A trace in ITF is a JSON object:

```js
{
  "#meta": <optional object>,
  "params": <optional array of strings>,
  "vars":  <array of strings>,
  "states": <array of states>,
  "loop": <optional int>
}
```

The field `#meta` is an arbitrary JSON object, whose purpose is to provide
the reader with additional comments about the trace. For example, it may look
like:

```js
  "#meta": {
    "description": "Generated by Apalache",
    "source": "MissionariesAndCannibalsTyped.tla"
  }
```

The optional field `params` is an array of names that must be set in the
initial state (if there are any parameters). The parameters play the same role
as `CONSTANTS` in TLA+. For example, the field may look like:

```js
  "params": [ "Missionaries", "Cannibals" ]
```

The field `vars` is an array of names that must be set in every state.
For example, the field may look like:

```js
  "vars": [ "bank_of_boat", "who_is_on_bank" ]
```

The field `states` is an array of state objects (see below). For example,
the field may look like:

```js
  "states": [ <state0>, <state1>, <state2> ]
```

The optional field `loop` specifies the index of the state (in the array of
states) that starts the loop. The loop ends in the last state. For example,
the field may look like:

```js
  "loop": 1
```

**State object**. A state is a JSON object:

```js
  {
    "#meta": <optional object>,
    "<var1>": <expr>,
    ...
    "<varN>": <expr>
  }
```

As in the trace object, the field `#meta` may be an arbitrary object.
Different tools may use this object to write their metadata into this object.

The names `<var1>, ..., <varN>` are the names of the variables that are
specified in the field `vars`. Each state must define a value for every specified variable. The syntax of `<expr>` is specified below. 

**Expressions.** As usual, expressions are inductively defined. An expression
`<expr>` is one of the following:

1. A JSON Boolean: either `false` or `true`.

1. A JSON string literal, e.g., `"hello"`. TLA+ strings are written as strings in this format.

1. A JSON integer, e.g., 123. According to [RFC7159][], JSON integers must be in the range: `[-(2**53)+1, (2**53)-1]`.
   Integers in this range *may be* written as JSON integers.

1. A big integer of the following form: `{ "#bigint": "[-][0-9]+" }`. We are using this format, as many JSON parsers
   impose limits on integer values, see [RFC7159][]. Big and small integers *may be*
   written in this format.

1. A list of the form `[ <expr>, ..., <expr> ]`. A list is just a JSON array. TLA+ sequences are written as lists in this format.

1. A record of the form `{ "field1": <expr>, ..., "fieldN": <expr> }`. A record is just a JSON object. Field names should not start with `#`
   and hence should not pose any collision with other constructs. TLA+ records are written as records in this format.

1. A tuple of the form `{ "#tup": [ <expr>, ..., <expr> ] }`. There is no strict rule about when to use sequences or tuples. Apalache differentiates
   between tuples and sequences, and it may produce both forms of expressions.

1. A set of the form `{ "#set": [ <expr>, ..., <expr> ] }`. A set is different from a list in that it does not assume any ordering of its elements. However,
   it is only a syntax form in our format. Apalache distinguishes between sets and lists and thus it will output sets in the set form. Other tools may
   interpret sets as lists.

1. A map of the form `{ "#map": [ [ <expr>, <expr> ], ..., [ <expr>, <expr> ]
   ] }`. That is, a map holds a JSON array of two-element arrays. Each two-element array `p` is interpreted as follows: `p[0]` is the map key and
   `p[1]` is the map value. Importantly, a key may be an arbitrary expression. It does not have to be a string or an integer. TLA+ functions are written as maps
   in this format.

1. An expression that cannot be serialized: `{ "#unserializable": "<string
representation>" }`. For instance, the set of all integers is represented with
`{ "#unserializable": "Int" }`. This should be a very rare expression, which
should not occur in normal traces. Usually, it indicates some form of an
error.

### ITF as input to Apalache
To be able to read ITF traces, Apalache demands the following:
  - The `#meta` field must be present
  - The `#meta` field must contain a field `varTypes`, which is an object, the keys of which are the variables declared in `vars`, and the values are string representations of their types (as defined in [ADR002]).

For example:
```js
"#meta": {
  "varTypes": { 
    "bank_of_boat": "Str", 
    "who_is_on_bank": "Str -> Set(PERSON)" 
  }
}
```

### Example

The counterexample to `NoSolution` may be written in the ITF format as follows:

```js
{
  "#meta": {
    "source": "MC_MissionariesAndCannibalsTyped.tla",
    "varTypes": { 
      "bank_of_boat": "Str", 
      "who_is_on_bank": "Str -> Set(PERSON)" 
    }
  },
  "vars": [ "bank_of_boat", "who_is_on_bank" ],
  "states": [
    {
      "#meta": { "index": 0 },
      "bank_of_boat": "E",
      "who_is_on_bank": {
        "#map": [
          [ "E", { "#set": [ "c1_OF_PERSON", "c2_OF_PERSON",
                             "m1_OF_PERSON", "m2_OF_PERSON" ] } ],
          [ "W", { "#set": [] } ]
        ]  
      }
    },
    {
      "#meta": { "index": 1 },
      "bank_of_boat": "W",
      "who_is_on_bank": {
        "#map": [
          [ "E", { "#set": [ "c1_OF_PERSON", "m1_OF_PERSON" ] } ],
          [ "W", { "#set": [ "c2_OF_PERSON", "m2_OF_PERSON" ] } ]
        ]  
      }
    },
    {
      "#meta": { "index": 2 },
      "bank_of_boat": "E",
      "who_is_on_bank": {
        "#map": [
          [ "E", { "#set": [ "c1_OF_PERSON",
                             "m1_OF_PERSON", "m2_OF_PERSON" ] } ],
          [ "W", { "#set": [ "c2_OF_PERSON" ] } ]
        ]  
      }
    },
    {
      "#meta": { "index": 3 },
      "bank_of_boat": "W",
      "who_is_on_bank": {
        "#map": [
          [ "E", { "#set": [ "c1_OF_PERSON" ] } ],
          [ "W", { "#set": [ "c2_OF_PERSON", "m1_OF_PERSON", "m2_OF_PERSON" ] } ]
        ]  
      }
    },
    {
      "#meta": { "index": 4 },
      "bank_of_boat": "E",
      "who_is_on_bank": {
        "#map": [
          [ "E", { "#set": [ "c1_OF_PERSON", "c2_OF_PERSON" ] } ],
          [ "W", { "#set": [ "m1_OF_PERSON", "m2_OF_PERSON" ] } ]
        ]  
      }
    },
    {
      "#meta": { "index": 5 },
      "bank_of_boat": "W",
      "who_is_on_bank": {
        "#map": [
          [ "E", { "#set": [ ] } ],
          [ "W", { "#set": [ "c1_OF_PERSON", "c2_OF_PERSON",
                             "m1_OF_PERSON", "m2_OF_PERSON" ] } ]
        ]  
      }
    }
  ]
}
```

Compare the above trace format with the TLA+ counterexample. The TLA+ example
looks more compact. The ITF example is heavier on the brackets and braces, but
it is also designed with machine-readability and tool automation in mind,
whereas TLA+ counterexamples are not.  However, the example in the ITF format
is also self-explanatory and does not require any understanding of TLA+.

Note that we did not output the operator `InvariantViolation` of the TLA+
example. This operator is simply not a part of the trace. It could be added in
the `#meta` object by Apalache.

### Discussion

Shon Feder @shonfeder flagged important concerns about irregularity of the
proposed format in the [PR
comments](https://github.com/informalsystems/apalache/pull/1190). In a
regular approach we would treat all expressions uniformly. For example:

```js
// proposed form:
"hello"
// regular form:
{ "#type": "string", "#value": "hello" }

// proposed form:
{ "#set": [ 1, 2, 3] }
// regular form:
{ 
  "#type": "set",
  "#value": [
    { "#type": "int", "#value": "1" },
    { "#type": "int", "#value": "2" },
    { "#type": "int", "#value": "3" }
  ]
}
```

The more regular approach is less concise. In the future, we might want to add
a flag that lets the user choose between the regular output and the output
proposed in this ADR, which is more ad hoc.

Another suggestion is to use [JSON
schema](https://cswr.github.io/JsonSchema/#what-is-json-schema?).  For the
moment, it seems to be a heavy-weight solution with no obvious value.  However,
we should keep it in mind and use schemas, when the need arises.


## Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

Reserved for the future.


[ADR005]: https://apalache.informal.systems/docs/adr/005adr-json.html
[ADR002]: https://apalache.informal.systems/docs/adr/002adr-types.html
[MissionariesAndCannibalsTyped]: https://github.com/informalsystems/apalache/blob/main/test/tla/MissionariesAndCannibalsTyped.tla
[JSON]: https://en.wikipedia.org/wiki/JSON
[RFC7159]: https://datatracker.ietf.org/doc/html/rfc7159.html
