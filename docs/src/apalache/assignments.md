# Assignments in Apalache
Any run of Apalache requires an operator name as the value for the parameter `--next` (by default, this value is `"Next"`). We refer to this operator as the _transition operator_ (or _transition predicate_).
## Actions, Slices and Minimal Actions
### Actions
In TLA+, an _action_ is any Boolean-valued expression or operator, that contains primed variables (e.g. `Next`). For the sake of this definition, assume `UNCHANGED x` is just syntactic sugar for `x' = x`.
Intuitively, actions are used to define the values of state variables after a transition, for example:
```tla
VARIABLE x
...

Next == x' = x + 1
```
The state transition described by `Next` is fairly obvious; if `x` has the value of `4` in the current state, it will have the value of `5` in any successor state.
This brings us to the first natural requirement by Apalache: *the transition operator must be an action.*

### Successor State Encodings
Unfortunately, the notion of an action is too broad to be a sufficient requirement for the transition operator.
Consider this slight modification of the above example:
```tla
VARIABLE x, y (* new variable *)
...

Next == x' = x + 1
```
Just as in the first example, the expression `x' = x + 1` is, by definition, an action. 
However, since the second example defines a state variable `y`, this action is 
no longer a sufficient description of a relation between a current state and a successor state; it does not determine a successor value `y'`.
This brings us to the second requirement: *the transition operator must allow Apalache to directly encode the relation between two successive states.*
This captures two sub-requirements: firstly, we disallow transition operators which fail to specify the value of one or more variables in the successor states, like the one in the example above. Secondly, we also disallow transition operators where the value of a successor state variable is determined only by implicit equations. Consider the following two cases:
```tla
VARIABLE y
...

A == y' = 1
B == y' * y' - 2 * y' + 1 = 0 
```
Using some basic math, we see that action `B` can be equivalently written as `(y' - 1)*(y' - 1) = 0`, so it describes the exact same successor state, in which the new value of `y` is `1`. 
What makes it different from action `A` is the fact that this is far from immediately obvious from the syntax. 
The fact that there happened to be a closed-form solution for which gave us an integer value for `y'`, is a lucky coincidence, as `B` could have been, for example, `y' * y' + 1 = 0`, with no real roots. 
To avoid cases like this, we require that transition operators explicitly declare the values of state variables in successor states.

We call syntactic forms, which explicitly represent successor state values, _assignment candidates_. An assignment candidate for `x` is a TLA+ expression that has one of the following forms:
- `x' = e`, 
- `x' \in S`,
- `UNCHANGED x`, or
- `x' := e` (note that `:=` is the operator defined in `Apalache.tla`)

So to reformulate the second requirement: the transition operator must contain at least one assignment candidate for each variable declared in the specification.

### Control Flow: Minimal and Compound Actions
When writing non-trivial specifications, authors often end up with something similar to the following:
```tla
EventA == ...
EventB == ...
...

Next == \/ EventA
        \/ EventB
```
Specifically, `EventA` and `EventB` often represent mutually exclusive possibilities of execution.
Just like before, the basic definition of an action is not sufficient to explain the relation of `EventA` or `EventB` and `Next`;
if `EventA` is an action and `EventB` is an action, then `Next` is also an action.
To more accurately describe this scenario, we observe that the operator or ( `\/`) sometimes serves as a kind of parallel composition operator (`||`) in process algebra - it connects two (or more) actions into a larger one.

There are only two operators in TLA+ that could be considered control-flow operators in this way, the or (`\/`) operator and the if-then-else operator.
We distinguish their uses as action- and as value operators:
```tla

A == x = 1 \/ x = 2 (* arguments are not actions *)
B == x' = 1 \/ x' = 2 (* arguments are actions *)
```
Simply put, if all arguments to an operator `\/` are actions, then that operator is an action-or, otherwise it is a value-or. Similarly, if both the `THEN _` and `ELSE _` subexpressions of if-then-else are actions, it is an action-ITE, otherwise it is a value-ITE (in particular, a value-ITE can be non-Boolean).

Using these two operators we can define the following terms:
A _minimal action_ is an action which contains no action-or and no action-ITE.
Conversely, a _compound action_ is an action which contains at least one action-or or at least one action-ITE.

### Slices
Given a transition operator, which is most commonly a compound action, we can decompose it into as many minimal actions as possible. We call this process _slicing_ and the resulting minimal actions _slices_.
This allows us to write transition operators in the following equivalent way:
```tla
Next == \/ Slice1
        \/ Slice2
        ...
        \/ SliceN
```
Where each `Slice[i]` is a minimal action.

The details of slicing are nuanced and depend on operators other than or (`\/`) and if-then-else, but we give two examples here:

If a formula `A` has the shape `A1 \/ ... \/ An` (where `A1`, ... `An` are actions), then a slice of A has the shape `Si`, where `Si` is a slice of some `Ai`.

If a formula `A` has the shape `IF p THEN A1 ELSE A2` (where `A1`, `A2` are actions), then a slice of A has the shape 
`p /\ S1` or `\neg p /\ S2`, where `S1` is a slice of `A1` and `S2` is a slice of `S2`.

Slices allow us to formulate the final requirement: the transition operator must be such, that we can select one assignment candidate for each variable in each of its slices (minimal actions) as an _assignment_. The process and conditions of selecting assignments from assignment candidates is described in the next section.

## <a id='asgn' /> Assignments and Assignment Candidates
Recall, an _assignment candidate_ for `x` is a TLA+ expression that has one of the following forms:
- `x' = e`, 
- `x' \in S`,
- `UNCHANGED x`, or
- `x' := e` (note that `:=` is the operator defined in `Apalache.tla`)

While a transition operator may contain multiple assignment candidates for the same variable, not all of them are chosen as _assignments_ by Apalache. The subsections below describe how the assignments are selected.

### Minimality
Assignments aren't spurious; each variable must have at least one assignment per transition operator, but no more than necessary to satisfy all of the additional constraints below (i.e. no more than one assignment per slice).

If all possible slices fail to assign one or more variables, an error, like the one below, is reported:
```
Assignment error: No assignments found for: x, z 
```

Such errors are usually the result of adding a `VARIABLE` without any accompanying TLA+ code relating to it. 
The case where at least one transition, but not all of them, fails to assign a variable is shown below.

### Syntax Order
For the purpose of evaluating assignments, Apalache considers the left-to-right syntax order of and-operator (`/\`) arguments. 
Therefore, as many assignments as possible are selected from the first (w.r.t. syntax order) argument of and (`/\`), then from the second, and so on.

Example:
```tla
Next == x' = 1 /\ x' = 2
```
In the above example, `x' = 1` would be chosen as an assignment to `x`, over `x' = 2`.

### Assignment-before-use Convention
If, in the syntax order defined above, an expression containing a primed variable `x'` syntactically precedes an assignment to `x`, the assignment finder throws an exception of the following shape:
```
Assignment error: test.tla:10:16-10:17: x' is used before it is assigned.
```
notifying the user of any variables used before assignment. In particular, right-hand-sides of assignment candidates ( e.g. `x' + 2` in `y' = x' + 2` )are subject to this restriction as well. Consider:
```tla
A == x' > 0 /\ x' = 1
B == y' = x' + 2 /\ x' = 1
```
In `A`, the expression `x' > 0` precedes any assignment to `x` and in `B`, while `y' = x' + 2` is an assignment candidate for `y`, it precedes any assignment to `x`, so both expressions are inadmissible (and would trigger exceptions). 

Note that this only holds true if `A` (resp. `B`) is chosen as the transition operator. If `A` is called inside another transition operator, for example in `Next == x' = 1 /\ A`, no error is reported.

### Balance
In cases of the or-operator (`\/`), all arguments must have assignments for the same set of variables. In particular, if one argument contains an assignment candidate and another does not, such as in this example:
```
\/ y = 1
\/ y' = 2
```
the assignment finder will report an error, like the one below:
```
Assignment error: test.tla:10:15-10:19: Missing assignments to: y
```
notifying the user of any variables for which assignments exist in some, but not all, arguments to `\/`. 
Note that if we correct and extend the above example to
```tla
/\ \/ y' = 1
   \/ y' = 2
/\ y' = 3
```
the assignments to `y` would be `y' = 1` and `y' = 2`, but not `y' = 3`; minimality prevents us from selecting all three, the syntax order constraint forces us to select assignments in `y' = 1 \/ y' = 2` before `y' = 3` and balance requires that we select both `y' = 1` and `y' = 2`.
On the other hand, if we change the example to
```tla
/\ y' = 3
/\ \/ y = 1
   \/ y' = 2
```
the only assignment has to be `y' = 3`. While one of the disjuncts is an assignment candidate and the other is not, the balance requirement is not violated here, since neither disjunct is chosen as an assignment.

Similar rules apply to if-then-else: both the `THEN _` and `ELSE _` branch must assign the same variables, however, the `IF _` condition is ignored when determining assignments.

### Assignment-free Expressions
Not all expressions may contain assignments. 
While Apalache permits the use of all assignment candidates, except ones defined with `:=`(details [here](#manual)), inside other expressions, some of these candidates will never be chosen as assignments, based on the syntactic restrictions outlined below:

 Given a transition operator `A`, based on the shape of `A`, the following holds:
- If `A` has the shape `A_1 /\ ... /\ A_n`, then assignments are selected from `A_1, ... , A_n` sequentially, subject to the syntax-order rule.
- If `A` has the shape `A_1 \/ ... \/ A_n`, then assignments are selected in all `A_1, ... , A_n` independently, subject to the balance rule.
- If `A` has the shape `IF p THEN A_1 ELSE A_2`, then:
    - `p` may not contain assignments. Any assignment candidates in `p` are subject to the assignment-before-use rule.
    - Assignments are selected in both `A_1` and `A_n` independently, subject to the balance rule.
- If `A` has the shape `\E x \in S: A_1`, then:
    - `S` may not contain assignments. Any assignment candidates in `S` are subject to the assignment-before-use rule.
    - Assignments are selected in `A_1`
- In any other case, `A` may not contain assignments, however, any assignment candidates in `A` are subject to the assignment-before-use rule.

Examples:
```tla
A == /\ x' = 2 
     /\ \E s \in { t \in 1..10 : x' > t }: y' = s
```
Operator `A` contains assignments to both `x` and `y`; while `x' > t` uses `x'`, it does not violate the assignment-before-use rule, since the assignment to `x` precedes the expression, w.r.t. syntax order.
```tla
(* INVALID *)
B == \E s \in { t \in 1..10 : x' > t }: y' = s
```
In operator `B`, the assignment to `x` is missing, therefore `x' > t` produces an error, as it violates assignment-before-use.
```tla
C == /\ x' = 1 
     /\ IF x' = 0 /\ 2 \in {x', x' + 2, 0}
        THEN y' = 1 
        ELSE y' = 2
```
The case in `C` is similar to `A`; conditions of the if-then-else operator may not contain assignments to `x`, so `x' = 0` can never be one, but they may use `x'`, since a preceding expression (`x' = 1`) qualifies as an assignment.
```tla
(* INVALID *)
D == IF x' = 0 
     THEN y' = 1 
     ELSE y' = 2
```
The operator `D` produces an error, for the same reason as `B`; even though `x' = 0` is an assignment candidate, if-conditions are assignment-free, so `x' = 0` cannot be chosen as an assignment to `x`.
```tla
(* INVALID *)
E == /\ x' = 2 
     /\ \A s \in { t \in 1..10 : x' > t }: y' = s
```
Lastly, while `E` looks almost identical to `A`, the key difference is that expressions under universal quantifiers may not contain assignments. Therefore, `y' = s` is *not* an assignment to `y` and thus violates assignment-before-use.

## <a id='manual' /> Manual Assignments
Users may choose, but aren't required, to use manual assignments `x' := e` in place of `x' = e`.
While the use of this operator does not change Apalache's internal search for assignments (in particular, using manual assignment annotations is *not* a way of circumventing the syntax order requirement), we encourage the use of manual assignments for clarity.

Unlike other shapes of assignment candidates, whenever a manual assignment is used in a position where the assignment candidate would not be chosen as an assignment (either within assignment-free expressions or in violation of, for example, the syntax order rule) an error, like one of the two below, is reported:
```
Assignment error: test.tla:10:12-10:18: Manual assignment is spurious, x is already assigned!
```
or 
```
Assignment error: test.tla:10:15-10:21: Illegal assignment inside an assignment-free expression.
```

The benefit of using manual assignments, we believe, lies in synchronizing the user's and the tool's understanding of where assignments happen. 
This helps prevent unexpected results, where the user's expectations or intuition regarding assignment positions are incorrect.

Note: To use manual assignments where the assignment candidate has the shape of `x' \in S` use `\E s \in S: x' := s`.