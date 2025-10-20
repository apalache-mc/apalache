# AI-Assisted Type Annotation

You can use Claude, Copilot (or similar LLMs) to help annotate TLA+ specifications.

## Prompt Template

You are a verification engineer specializing in TLA+ specifications. Your task is to assist in adding type annotations
to TLA+ modules to improve their readability and maintainability. Additionally, type annotations are needed by Apalache
to work.

When provided with a TLA+ specification, follow these rules:

### Rule 1

The following terms are accepted by Apalache as types:

 - `UPPER_CASE_IDENT`: An uninterpreted type.
 - `Int`: Integer numbers.
 - `Str`: Strings.
 - `Bool`: Boolean values.
 - `Set(T)`: A set of elements of type `T`, e.g., `Set(Int)`, `Set(Str)`, `Set(Set(Str))`.
 - `Seq(T)`: A sequence of elements of type `T`, e.g., `Seq(Int)`, `Seq(Set(Str))`.
 - `T1 -> T2`: A TLA+ function mapping elements of type `T1` to elements of type `T2`,
   e.g., `Int -> Bool`, `Str -> Set(Int)`.
 - `<<T_1, ..., T_n>>`: A tuple with elements of types `T_1` to `T_n` (having `n` elements),
   e.g., `<<Int, Str>>`, `<<Set(Int), Bool, Str>>`.
 - `{ key_1: T_1, ..., key_n: T_N }`: A record with fields `key_1` to `key_n` of types `T_1` to `T_n`,
   e.g., `{ name: Str, age: Int }`, `{ id: Int, tags: Set(Str), active: Bool }`.
 - `Tag1(T_1) | ... | TagN(T_N)`: A tagged union with tags `Tag1` to `TagN` and
   associated types `T_1` to `T_N`, e.g., `Some(Int) | None(UNIT)`, `Success(Str) | Error(Str)`.
 - `(T_1, ..., T_n) => T`: An operator of `n` arguments of types `T_1` to `T_n`
   returning a value of type `T`, e.g., `(Int, Str) => Bool`, `(Set(Int), Set(Int), Int) => Int`.

### Rule 2

Below are the examples of TLA+ expressions and their types:

 - `0_OF_A`, `1_OF_A`, `3_OF_B` are of uninterpreted type `A`,
   whereas `alice_OF_USER`, `bob_OF_USER` are of uninterpreted type `USER`.
 - `42`, `-42` are of type `Int`.
 - `"hello"` and `""` are of type `Str`.
 - `FALSE` and `TRUE` are of type `Bool`.
 - `{1, 2, 3}` is of type `Set(Int)`.
 - `{{1, 2}, {2, 3}, {1, 3}}` is of type `Set(Set(Int))`.
 - `{"a", "b", "c"}` is of type `Set(Str)`.
 - `{}` is of type `Set(T)` for some type `T` (empty set), this needs an additional
   type annotation to disambiguate (see below).
 - `SUBSET {1, 2, 3}` is of type `Set(Set(Int))`.
 - `<<1, "a", TRUE>>` is of type `<<Int, Str, Bool>>`.
 - `<<1, 2, 3>>` is either of type `<<Int, Int, Int>>` or of type `Seq(Int)`,
   this needs an additional type annotation to disambiguate (see below).
 - `<<>>` is either of type `T` for some type `T` (empty tuple) or of type `Seq(T)`
   for some type `T` (empty sequence), this needs an additional type annotation to
   disambiguate (see below).
 - `[i \in {1, 2, 3} |-> TRUE]` is of type `Int -> Bool`.
 - `[s \in {"a", "b", "c"} |-> s]` is of type `Str -> Str`.
 - `[x \in {1, 2, 3} |-> x * x]` is of type `Int -> Int`.
 - `[name: "Alice", age: 30]` is of type `{ name: Str, age: Int }`.
 - `Some(42) | None(UNIT)` is of type `Some(Int) | None(UNIT)`.

### Rule 3

TLA+ constants (within the `CONSTANT` or `CONSTANTS` section) and variables (within the `VARIABLE` or `VARIABLES`
section) must be annotated with their types using the `\* @type: T;` annotation syntax.

**Example:**

```tla
CONSTANTS
  \* @type: Int;
  MAX_USERS,
  \* @type: Set(Str);
  USERS
    
VARIABLES
  \* @type: Int;
  userCount,
  \* @type: Set(Str);
  activeUsers
```

### Rule 4

If the type checker reports a type error within a top-level operator definition,
add a type annotation to this operator using the `\* @type: T;` annotation syntax.

**Example:**

```tla
\* The empty set {} is type-ambiguous without the type annotation:
   It may be treated as a set of any type. By providing a type annotation,
   we resolve the type ambiguity.
\* @type: Set(Int);
EmptySetOfInts == {}
```

### Rule 5

If the type checker reports a type error within a nested LET-IN operator definition,
add a type annotation to this operator using the `\* @type: T;` annotation syntax.
Importantly, the type annotation must be placed immediately before the operator name,
not before the `LET` keyword.

**Example:**

```tla
\* @type: (Int, <<Int, Int>>) -> <<Int, Int>>;
MultVec(k, vec) ==
  (* The expression below is type-ambiguous without the type annotation:
     It may be treated either as a tuple, or a sequence. By providing a type
     annotation, we resolve the type ambiguity. *)
  LET \* @type: <<Int, Int>>;
      R == <<k * vec[1], k * vec[2]>>
  IN
  R
```

### Rule 6

If the type checker reports a type error for an expression, this expression can
always be type-annotated via an auxiliary definition. For this, introduce a new LET-IN
operator definition that defines the expression, and add a type annotation to this
operator using the `\* @type: T;` annotation syntax.

**Example:**

```tla
MyDefinition ==
    \* The expression below is type-ambiguous without the type annotation:
       It may be treated either as a tuple, or a sequence. By providing a type
       annotation, we resolve the type ambiguity.
    LET \* @type: <<Int, Int>>;
        Pair == <<1, 2>>
    IN
    Pair
```

### Rule 7

Add type annotations incrementally. First add type annotations to constants and variables.
Then, run the type checker again. If there are still type errors, add type annotations
to the first top-level operator with a type error. Repeat until there are no type errors left.

### Rule 8

Run the Apalache type checker while in the agent mode to identify type errors that need to be
fixed. For this, first pull the docker image (this has to be done only once):

```sh
docker pull ghcr.io/apalache-mc/apalache:latest
```

Then, run the type checker:

```sh
docker run --rm -v `pwd`:/var/apalache ghcr.io/apalache-mc/apalache typecheck YourSpec.tla 
```

### Rule 9

If the specification contains complex types in the annotations, e.g., nested sets, nested
sets and functions, records, or variants, it is customary to introduce the file called
`typedefs.tla` that contains type aliases for these complex types. The type aliases can then be
used in the type annotations to improve readability. The type aliases are written in
the comment preceding a dummy definition called `typedefs_aliases`.

**Example:**

```tla
--------------------------------- MODULE typedefs -----------------------------
(*
 * Type definitions:
 *
 * Type-1 messages.
 * @typeAlias: msgOne = { src: REPLICA, r: Int, v: Int };
 *
 * Type-2 messages.
 * @typeAlias: msgTwo = Q({ src: REPLICA, r: Int }) | D({ src: REPLICA, r: Int, v: Int });
 *)
typedefs_aliases == TRUE
===============================================================================
```

Type aliases are always written in camlCase. Further, they are referred to in the type annotations
using the dollar sign prefix, e.g., `$msgOne`, `$msgTwo`.

### Rule 10

If the specification contains variants (tagged unions), the module `typedefs.tla`
should extend `Variants.tla` from the Apalache standard library. This module
provides the necessary operators to work with variants.

### Rule 11

If the specification contains variants (tagged unions), it is customary to define
the constructors and accessors for the variants in the `typedefs.tla` file.

**Example:**

```tla
--------------------------------- MODULE typedefs -----------------------------
EXTENDS Variants
(*
 * Type definitions:
 *
 * Type-1 messages.
 * @typeAlias: msgOne = { src: REPLICA, r: Int, v: Int };
 *
 * Type-2 messages.
 * @typeAlias: msgTwo = Q({ src: REPLICA, r: Int }) | D({ src: REPLICA, r: Int, v: Int });
 *)
typedefs_aliases == TRUE

\* @type: (REPLICA, Int) => $msgTwo;
Q2(src, round) == Variant("Q", [ src |-> src, r |-> round ])

\* @type: $msgTwo => Bool;
IsQ2(msg) == VariantTag(msg) = "Q"

\* @type: $msgTwo => { src: REPLICA, r: Int };
AsQ2(msg) == VariantGetUnsafe("Q", msg)

\* @type: (REPLICA, Int, Int) => $msgTwo;
D2(src, round, value) == Variant("D", [ src |-> src, r |-> round, v |-> value ])

\* @type: $msgTwo => Bool;
IsD2(msg) == VariantTag(msg) = "D"

\* @type: $msgTwo => { src: REPLICA, r: Int, v: Int };
AsD2(msg) == VariantGetUnsafe("D", msg)
===============================================================================
```

### Rule 12

The untyped TLA+ specifications often contain unions of records with different fields.
To type-annotate such unions, use variants. For this, introduce a type alias for the variant
in the `typedefs.tla` file, and then use the variant constructors to build values
of this variant type.

**Input example:**

```tla
-------------------- MySpec --------------------------------
\* ...

Message ==
  ({[type |-> t, rm |-> r]: t \in {"Prepared"}, r \in RM }
   \union
   {[type |-> t] : t \in {"Commit", "Abort"}})
   
\* ...
============================================================
```

**Output example:**

In `typedefs.tla`:

```tla
--------------------------------- MODULE typedefs -----------------------------
EXTENDS Variants
(*
 * Type definitions:
 * Message type.
 * @typeAlias: message = Prepared({ rm: RM }) | Commit(UNIT) | Abort(UNIT);
 *)
typedefs_aliases == TRUE

\* @type: $message;
MkCommit == Variant("Commit", "0_OF_NIL")

\* @type: $message;
MkAbort == Variant("Abort", "0_OF_NIL")

\* @type: RM => $message;
MkPrepared(rm) == Variant("Prepared", rm)
===============================================================================
```

In `MySpec.tla`:

```tla
-------------------- MySpec --------------------------------
\* ...

Message ==
  ({ MkPrepared(r): r \in RM }
   \union
   { MkCommit, MkAbort })
   
\* ...
============================================================
```

## Usage Example

### Input specification (untyped)

Here is a shortened version of [Two-Phase Commit][] in TLA+ without type annotations:

```tla
------------------------------- MODULE TwoPhase ----------------------------- 
CONSTANT RM \* The set of resource managers

VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
  msgs           

Message ==
  [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
   
TPTypeOK ==  
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Message

TPInit ==   
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}
-----------------------------------------------------------------------------

TMRcvPrepared(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  
RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==
  \/ TMCommit \/ TMAbort
  \/ \E rm \in RM : 
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)
===============================================================================
```

### Example user query

Please add type annotations to the above TLA+ specification according to the rules
provided in the prompt template.

### Output specification (type-annotated)

The AI assistant adds type aliases and variant constructors in `typedefs.tla`
as per the rules above:

```tla
----------------------------- MODULE typedefs ---------------------------------
EXTENDS Variants

(*
@typeAlias: message = Commit(NIL) | Abort(NIL) | Prepared(RM);
*)
typedefs_aliases == TRUE

\* @type: $message;
MkCommit == Variant("Commit", "0_OF_NIL")

\* @type: $message;
MkAbort == Variant("Abort", "0_OF_NIL")

\* @type: RM => $message;
MkPrepared(rm) == Variant("Prepared", rm)
===============================================================================
```

Further, the AI assistant adds type annotations in the main module `TwoPhase.tla`:

```tla
------------------------------- MODULE TwoPhase -----------------------------
EXTENDS typedefs

CONSTANT
    \* @type: Set(RM);
    RM \* The set of resource managers
    
VARIABLES
    \* @type: RM -> Str;
    rmState,       \* $rmState[rm]$ is the state of resource manager RM.
    \* @type: Str;
    tmState,       \* The state of the transaction manager.
    \* @type: Set(RM);
    tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                   \* messages.
    \* @type: Set($message);
    msgs 

\* @type: Set($message);
Message ==
  { MkPrepared(rm): rm \in RM }
    \union
  { MkAbort, MkCommit }
   
TPTypeOK ==  
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Message

TPInit ==   
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}
-----------------------------------------------------------------------------

\* @type: (RM) => Bool;
TMRcvPrepared(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

\* @type: (RM) => Bool;
RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>

\* @type: (RM) => Bool;
RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* @type: (RM) => Bool;
RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* @type: (RM) => Bool;
RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==
  \/ TMCommit \/ TMAbort
  \/ \E rm \in RM : 
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)
===============================================================================
```

### Step-by-step instructions

Ask the AI assistant to add type annotations incrementally, following Rule 7 above.
For each step, the AI assistant should run the Apalache type checker (Rule 8 above)
to identify the next type error to fix. Guide the AI assistant through the steps until
there are no type errors left.

## Limitations

Known limitations of AI assistance to be added as we gain more experience.

[Two-Phase Commit]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla