# Idiom 7: Use Boolean operators in actions, not `IF-THEN-ELSE`

**author:** Gabriela Moreira

## Description

TLA+ provides an `IF-THEN-ELSE` operator, and it can be pretty tempting to use it for flow control,
as it's done in procedural programming.
However, TLA+ is about transitions over a state machine,
and a transition-defining action declared with `IF-THEN-ELSE` can be more complex than 2 actions declared without it.
Considering that any expression of the form `IF b THEN x ELSE y`, where `x` and `y` are Booleans,
can be rewritten as `(b /\ x) \/ (~b /\ y)`,
there's a pattern we can apply to get rid of some potentially troublesome `IF-THEN-ELSE` definitions.

The `IF-THEN-ELSE` operator can be used either to define a value, or to branch some action as a sort of flow control.
Defining values with `IF-THEN-ELSE` is common practice
and is similar to the use of `IF` expressions in declarative programming languages.
However, flow control in TLA+ can be done naturally by behavior definition through actions,
making the use of `IF-THEN-ELSE` for flow control unnecessary.
This idiom aims to clarify different usages of `IF-THEN-ELSE` expressions,
keeping in mind the TLA+ essence of declaring actions to define transitions. 

## When to use `IF-THEN-ELSE`

### When the result is not Boolean

When the `IF-THEN-ELSE` expression doesn't evaluate to a Boolean value,
it cannot be rewritten using Boolean operators, so this idiom doesn't apply.
For example:

```tla
SafeDiv(x, y) == IF y /= 0 THEN x/y ELSE 0
```

### When the result is a state formula

State formulas are formulas that don't contain any action operator (e.g. primed variables, `UNCHANGED`).
Using `IF-THEN-ELSE` on this type of formula can make it easier to read in some situations,
and don't come with any disadvantage.
This example state formula uses `IF-THEN-ELSE` to return a Boolean value: 

```tla
ValidIdentity(person) == IF Nationalized(person) THEN ValidId(person) ELSE ValidPassport(person)
```

Although it could be rewritten with Boolean operators, it doesn't read as nicely:

```tla
ValidIdentity(person) == \/ /\ Nationalized(person)
                            /\ ValidId(person)
                         \/ /\ ~Nationalized(person)
                            /\ ValidPassport(person)
```

## When there are dependent conditions

Nesting `IF-THEN-ELSE` expressions can be useful when there is a dependency between the conditions
where some conditions are only relevant if other conditions are met.
This is an example where using an `IF-THEN-ELSE` expressions is clearer than the Boolean operator form.
Consider the following:

```tla
IF c1
THEN a1
ELSE IF c2
THEN a2
ELSE IF
...
ELSE IF cn
THEN an
ELSE a 
```

The Boolean operator version is quite verbose:

```tla
\/ c1 /\ a1
\/ ~c1 /\ c2 /\ a2
\/ ...
\/ ~c1 /\ ... /\ ~c_{n-1} /\ cn /\ an
\/ ~c1 /\ ... /\ ~c_{n-1} /\ ~cn /\ a
```

## When (and how) *not* to use `IF-THEN-ELSE`

Mixing `IF-THEN-ELSE` expressions with action operators introduces unnecessary branching to definitions
that could be self-contained and look more like a transition definition. 

```tla
Withdraw(amount) == IF balance >= amount 
                     THEN /\ balance' = balance - amount
                          /\ response' = "SUCCESS"
                     ELSE /\ UNCHANGED balance
                          /\ response' = "FAILURE"
```

We could separate the two branches into their own actions with clarifying names and explicit conditions,
and use a disjunction between the two actions instead of the `IF-THEN-ELSE` block:

```tla
WithdrawSuccess(amount) == /\ balance >= amount 
                           /\ balance' = balance - amount
                           /\ response' = "SUCCESS"
                            
WithdrawFailure(amount) == /\ balance < amount 
                           /\ response' = "FAILURE"
                           /\ UNCHANGED balance 
                            
Withdraw(amount) == WithdrawSuccess(amount) \/ WithdrawFailure(amount)
```

## Advantages

- Each action declares fewer transitions, so it's easier to reason about it
- A disjunction of actions is closer to a union of transition relations than an `IF-THEN-ELSE` expression is
- Nested `IF-THEN-ELSE` expressions are an extrapolation of these problems and can over-constrain some branches if not done carefully.
  Using different actions defining its conditions explicitly leaves less room for implicit wrong constraints
  that an `ELSE` branch allows.
  See the example below.

Assuming `C1()` is a condition for `A1()` and `C2()` is a condition for `A2()`:

```tla
Next == IF C1() 
          THEN A1()
          ELSE 
            IF C2() 
              THEN A2()
              ELSE A3()
```

What if `C1() /\ C2()` is true? In this case, only `A1()` would be enabled, which is incorrect. 

```tla
Next == \/ /\ C1()
           /\ A1()
        \/ /\ C2()
           /\ A2()
        \/ A3()
           
```

This second definition can allow more behaviors than the first one (depending on whether `C1()` and `C2()` overlap),
and these additional behaviors can be unintentionally left out when `IF-THEN-ELSE` is used without attention.

## Disadvantages

A disjunction in TLA+ may or may not represent non-determinism, while an `IF-THEN-ELSE` is incapable of introducing non-determinism.
If it's important that readers can easily differentiate deterministic and non-deterministic definitions,
using `IF-THEN-ELSE` expressions can help to make determinism explicit.
