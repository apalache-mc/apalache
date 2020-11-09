# Idiom 2: Apply primes only to state variables

(_Until you learn how prime actually works!_)

## Description

In many formal languages, the notation `x'` denotes the value that a variable
`x` has after the system has fired a transition. The reason for having both `x`
and `x'` is that the transitions are often described as relations over unprimed
and primed variables, e.g., `x' = x+1`. It is easy to extend this idea to
vectors of variables, but for simplicity we will use only one variable.

TLA+ goes further and declares prime (`'`) as an operator! Assume that we
evaluate a TLA+ expression `A` over `x` and `x'`, and `v[i]` and `v[i+1]` are
meant to be the values of `x` in the ith state and i+1-th state, respectively.
Then `x` is evaluated to `v[i]` and `x'` is evaluated to `v[i+1]`.  Naturally,
`x + 3` is evaluated to `v[i] + 3`, whereas `x' + 4` is evaluated to `v[i+1] +
4`. We can go further and evaluate `(x + 4)'`, which can be rewritten as `x' +
4`.

Intuitively, there is nothing wrong with the operator "prime". However, you
have to understand this operator well, in order to use it right. For starters, check
the warning by Leslie Lamport in [Specifying Systems] on page 82. The following
example illustrates the warning:

```tla
--------------------------- MODULE clocks3 ------------------------------------
(* Model a system of three processes, each one equipped with a logical clock *)
EXTENDS Integers, Apalache
VARIABLES clocks, turn

\* a shortcut to refer to the clock of the process that is taking the step
MyClock == clocks[turn]
\* a shortcut to refer to the processes that are not taking the step
Others == DOMAIN clocks \ {turn}

Init ==
    /\ clocks := [p \in 1..3 |-> 0]  \* initialize the clocks with 0
    /\ turn := 1                     \* process 1 makes the first step

Next ==
    \* update the clocks of the processes (the section Example shows a better way)
    /\ \E f \in [1..3 -> Int]:
        clocks' := f
    \* increment the clock of the process that is taking the step
    /\ MyClock' = MyClock + 1
    \* all clocks of the other processes keep their clock values
    /\ \A i \in Others:
        clocks'[i] = clocks[i]
    \* use round-robin to decide who makes the next step
    /\ turn' := 1 + (turn + 1) % 3
===============================================================================
```

Did you spot a problem in the above example? If not, check these lines again:

```tla
    \* increment the clock of the process that is taking the step
    /\ MyClock' = MyClock + 1
```

The code does not match the comment. By writing `MyClock'`, we get
`(clocks[turn])'` that is equivalent to `clocks'[turn']`. So our constraint
says: Increment the clock of the process that is taking the next step.  By
looking at the next constraint, we can see that `Next` can never be evaluated
to true (a logician would say that `Next` is "unsatisfiable"):

```tla
    \* all clocks of the other processes keep their clock values
    /\ \A i \in Others:
        clocks'[i] = clocks[i]
```

Our intention was to make the specification easier to read, but instead we have
introduced a deadlock in the system. In a larger specification, this bug would be
much harder to find.

We recommend to follow this simple rule: _Apply primes only to state variables_

Can we remove the "prime" operator altogether and agree to use `x` and `x'` as
names of the variables? Not really. More advanced features of TLA+ require this
operator.  In a nutshell, TLA+ is built around the idea of refinement, that is,
replacing an abstract specification with a more detailed one. Concretely, this
idea is implemented by module instances in TLA+. It often happens that
refinement requires us to replace a state variable of the abstract
specification with an operator of the detailed specification.  Voilà. You have
to apply prime to an expression. For the details, 
see Chapter 5 and pages 312-313 of [Specifying Systems].

## Advantages

 - It is easy to see, whether the specification author intended to talk about
   the variables in the next state or about the variable in the current state.

 - It is harder to make an unexpected substitution mistake, as in the above
   example.

## Disadvantages

 - Sometimes, the operator "prime" helps us in avoiding code duplication.
   For instance, you can write a state invariant `Inv` and later evaluate it
   against a next state by simply writing `Inv'`. However, you have to be
   careful about propagation of primes in `Inv`.

## Example

A better version of the `clocks` example applies prime only to state variables.
By doing so, we notice that the specification can be further simplified:

```tla
--------------------------- MODULE clocks3_2 ----------------------------------
(* Model a system of three processes, each one equipped with a digital clock *)
EXTENDS Integers, Apalache
VARIABLES clocks, turn

Init ==
    /\ clocks := [p \in 1..3 |-> 0]  \* initialize the clocks with 0
    /\ turn := 1                     \* process 1 makes the first step

Next ==
    \* update the clocks of the processes
    /\ clocks' :=
        [p \in 1..3 |->
            IF p = turn THEN clocks[turn] + 1 ELSE clocks[p]]
    \* use round-robin to decide who makes the next step
    /\ turn' := 1 + (turn + 1) % 3
===============================================================================
```



[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html

