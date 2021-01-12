# Idiom 1: Update state variables with assignments
For each TLA+ variable `x` defined in a specification, Apalache requires that every possible  transition defines an assignment to `x'`.

## Assignments and Assignment Candidates
An _assignment candidate_ for `x` is an expression that has one of the following forms:
- `x' = e`, 
- `x' \in e`,
- `UNCHANGED x`, or
- `x' := e`

While a transition may contain multiple assignment candidates for the same variable, not all of them are chosen as _assignments_ by Apalache. The sections below describe how the assignments are selected.

### Minimality
Assignments aren't spurious; each variable must have at least one assignment per transition operator, but no more than necessary to satisfy all of the additional constraints below.

If all possible transitions fail to assign one or more variables, an exception of the following shape is thrown:
```
Assignment error: No assignments found for: x, z 
```

Such exceptions are usually the result of adding a `VARIABLE` without any accompanying TLA+ code relating to it. 
The case where at least one transition, but not all of them, fails to assign a variable is shown below.

### Syntax Order
For the purpose of evaluating assignments, Apalache considers the left-to-right syntax order of conjuncts. 
Therefore, as many assignments as possible are selected from the first (w.r.t. syntax order) conjunct, then from the second, and so on.

Example:
```tla
Next == x' = 1 /\ x' = 2
```
In the above example, `x' = 1` would be chosen as an assignment to `x`, over `x' = 2`.

### Assignment-before-use Paradigm
If, in the syntax order defined above, an expression containing a primed variable `x'` precedes an assignment to `x`, the assignment finder throws an exception of the following shape:
```
Assignment error: test.tla:10:16-10:17: x' is used before it is assigned.
```
notifying the user of any variables used before assignment. In particular, right-hand-sides of assignment candidates are subject to this restriction as well. Consider:
```tla
A == x' > 0 /\ x' = 1
B == y' = x' + 2 /\ x' = 1
```
In `A`, the expression `x' > 0` precedes any assignment to `x` and in `B`, while `y' = x' + 2` is an assignment candidate for `y`, it precedes any assignment to `x`, so both expressions are inadmissible (and would trigger exceptions). 

Note that this only holds true if `A` (resp. `B`) is chosen as the transition operator. If `A` is called inside another transition operator, for example in `Next == x' = 1 /\ A`, no exception is thrown.

### Balance
In cases of disjunction, both (resp. all) disjuncts must have assignments for the same set of variables. In particular, if one disjunct contains an assignment candidate and another does not, such as in this example:
```tla
/\ \/ y = 1
   \/ y' = 2
/\ y' = 3
```
the assignment finder will throw an exception of the following shape:
```
Assignment error: test.tla:10:15-10:19: Missing assignments to: y
```
notifying the user of any variables for which assignments exist in some, but not all, disjuncts. 
Note that if we correct the above example to
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
Not all expressions may contain assignments. Given a transition operator `A`, based on the shape of `A`, the following holds:
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

B == \E s \in { t \in 1..10 : x' > t }: y' = s

C == /\ x' = 1 
     /\ IF x' = 0 /\ 2 \in {x', x' + 2, 0}
        THEN y' = 1 
        ELSE y' = 2

D == IF x' = 0 
     THEN y' = 1 
     ELSE y' = 2

E == /\ x' = 2 
     /\ \A s \in { t \in 1..10 : x' > t }: y' = s
```
Operator `A` contains assignments to both `x` and `y`; while `x' > t` uses `x'`, it does not violate the assignment-before-use rule, since the assignment to `x` precedes the expression, w.r.t. syntax order.
In operator `B`, the assignment to `x` is missing, therefore `x' > t` produces an exception, as it violates assignment-before-use.
The case in `C` is similar to `A`; conditions of the if-then-else operator may not contain assignments to `x`, so `x' = 0` can never be one, but they may use `x'`, since a preceding expression (`x' = 1`) qualifies as an assignment.
The operator `D` produces an exception, for the same reason as `B`; even though `x' = 0` is an assignment candidate, if-conditions are assignment-free, so `x' = 0` cannot be chosen as an assignment to `x`.
Lastly, while `E` looks almost identical to `A`, the key difference is that expressions under universal quantifiers may not contain assignments. Therefore, `y' = s` is *not* an assignment to `y` and thus violates assignment-before-use.

## Manual Assignments
Users may choose, but aren't required, to use manual assignments `x' := e` in place of `x' = e`.
While the use of this operator does not change Apalache's internal search for assignments (in particular, using manual assignment annotations is *not* a way of circumventing the syntax order requirement), we encourage the use of manual assignments for clarity.

Unlike other shapes of assignment candidates, whenever a manual assignment is used in a position where the assignment candidate would not be chosen as an assignment (either within assignment-free expressions or in violation of, for example, the syntax order rule) an  exception of the following shape is thrown:
```
Assignment error: test.tla:10:12-10:18: Manual assignment is spurious, x is already assigned!
```
or 
```
Assignment error: test.tla:10:15-10:21: Illegal assignment inside an assignment-free expression.
```

The benefit of using manual assignments, we believe, lies in synchronizing the user's and the tool's understanding of where assignments happen and can help prevent unexpected results, where the user's expectations or intuition regarding assignment positions are incorrect.

Note: To use manual assignments where the assignment candidate has the shape of `x' \in e` use `\E s \in e: x' := s`.