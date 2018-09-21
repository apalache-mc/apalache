Here is the list of the TLA+ language features that are currently supported by our model checker, following the [Summary of TLA+][cheat].

## Language

### Module-Level constructs

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
EXTENDS module | ✔ | - | As soon as SANY can import the module. Some standard modules are not supported yet
CONSTANTS C1, C2 | ✖ | -  | Declare your constants as operators, e.g., C1 == 111
VARIABLES x, y, z | ✔ | - |
ASSUME P | ✖ | - |
F(x1, ..., x_n) == exp | ✔ / ✖ | - | Provisionally, any use of F is replaced with its body. Hence, recursive operators are not supported.
f[x \in S] == exp | ? | - | A global function is replaced by an equivalent operator declaration. This feature has not been tested yet.
INSTANCE M WITH ... | ✖ | - | 
N(x1, ..., x_n) == INSTANCE M WITH... | ✖ | - |
THEOREM P | ✖ | - | 
LOCAL def | ✔ | - | Handled by SANY 

### The constant operators

#### Logic

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
∧, ∨, ¬, ⇒, ⇔, ≡ | ✔ | - |
TRUE, FALSE, BOOLEAN | ✔ | - |
∀x ∈ S: p, ∃x ∈ S : p |  ✔ | - | Multiple arguments might fail to work, as the tuples are not really supported yet. Just write ∀x ∈ S: ∀y ∈ T: p instead.
CHOOSE x ∈ S : p |  ✖ | - | We know how to implement it
∀x : p, ∃x : p |  ✖ | - | It is unlikely that we will support it, ever
CHOOSE x : p |  ✖ | - | It is unlikely that we will support it, ever


#### Sets

*Note that only the finite sets are supported*.

In the following, we sometimes denote sets as:
 
 * explicit, that is, constructed with {...} and the standard set operators such as union, intersection, comprehension, etc.
 * symbolic, that is, constructed with SUBSET S or [S -> T].

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
=, ≠, ∈, ∉, ⋂, ⋃, ⊆, \  | ✔ | - |
{e_1, ..., e_n} | ✔ | - |
{x ∈ S : p} | ✔ / ✖ | - | It may fail to work with tuples
{e : x ∈ S} | ✔ / ✖ | - | It may fail to work with tuples
SUBSET S | ✔ | - | Provided that S is *explicit*. Produces a *symbolic* set.
UNION S |  ✔ | - | Provided that S is *explicit*

#### Functions

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
f[e] | ✔ | - |
DOMAIN f | ✔ | - |
[ x ∈ S ↦ e] | ✔ / ✖ | - | It may fail to work with tuples
[ S → T ] | ✔ | - | Produces a *symbolic* set
[ f EXCEPT ![e1] = e2 ] | ✔ | - | 

#### Records

*Records require a decent type inference engine. This is work in progress. Simple record operations might work, but the current type inference engine often fails on sets that mix apples and oranges.*

Note that it is unlikely that we will allow the user to treat records as functions.

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
e.h | ✔ | - |
r[e] | ✔/✖ | - | Provided that e is a constant expression.
[ h1 ↦ e1, ..., h_n ↦ e_n] | ✔ | - |
[ h1 : S1, ..., h_n : S_n] | ✖ | - |
[ r EXCEPT !.h = e] | ✔ | - |

#### Tuples

*Tuples also require a decent type inference engine, in order to distinguish them from sequences. This is work in progress.*

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
e[i] | ✔ / ✖ | - | Provided that i is a constant expression
<< e1, ..., e_n >> | ✔ | - | Currently, this expression is always producing a tuple, not a sequence
S1 x ... x S_n | ✖ | - | This is just unfortunate that we have not implemented it yet.

#### Strings and numbers

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
"c1...c_n" | ✔ | - | A string is always mapped to a unique uninterpreted constant
STRING | ✖ | - | It is an infinite set. We cannot handle infinite sets.
d1...d_n | ✔ | - | As long as the SMT solver (Z3) accepts that large number
d1...d_n.d_n+1...d_m | ✖ | - | Technical matter. We could have implemented it.

#### Miscellaneous Constructs

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
IF p THEN e1 ELSE e2 | ✔ | - | Provided that both e1 and e2 have the same type
CASE p1→ e1 ▢ ... ▢ p_n → e_n | ✔ | - | Provided that all the expressions have the same type. Similar to TLC, the case expression is translated to series of IF-THEN-ELSE expressions.
CASE p1→ e1 ▢ ... ▢ p_n → e_n ▢ OTHER → e | ✔ | - | See the comment above
LET d1 == e1 ... d_n == e_n IN e | ✔ / ✖ | - | Provisionally, all usages of d1, ..., d_n are replaced with the expressions e1, ... e_n respectively.
multi-line /\ and \/ | ✔ | - | 

### The Action Operators

Construct  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
e' | ✔ / ✖ | - | Provided that e is a variable
[A]_e | ✖ | - | It does not matter for safety
< A >_e | ✖ | - |
ENABLED A | ✖ | - |	
UNCHANGED e | ✔ | - |	Always replaced with e' = e
A ∙B | ✖ | - |
	
### The Temporal Operators
	
The model checker assumes that the specification has the form Init /\ ▢[Next]_e. Given an invariant candidate Inv, the tool checks, whether Inv is violated by an execution whose length is bounded by the given argument.

Except the standard form Init /\ ▢[Next]_e, no temporal operators are supported.

## Standard modules

### Integers and Naturals

For the moment, the model checker does not differentiate between integers and naturals. They are all translated as integers in SMT.

**TODO: explicitly add the constraint x >= 0 for the naturals.**

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
+, -, *, <=, >=, <, > | ✔ | - | These operators are translated into integer arithmetic of the SMT solver. Linear integer arithmetic is preferred.
/, % | ✔ | - | Integer division and modulo
÷ | ✖ | - | Real division, not supported
a..b, a^b | ✔ / ✖ | - | Provided a and b are constant expressions
Int, Nat | ✖ | - | Infinite sets are not supported

### Reals

Not supported, not a priority

### Sequences

Not supported yet, but will be as soon as we have a decent type inference engine.

### FiniteSets

Operator  | Supported? | Milestone | Comment
------------------------|:------------------:|:---------------:|--------------
IsFinite | ✔ | - | Always returns true, as all the supported sets are finite
Cardinality | ✖ | - | A good encoding in SMT requires some research




[cheat]: https://lamport.azurewebsites.net/tla/summary.pdf
