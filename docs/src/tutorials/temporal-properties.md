# Temporal properties and counterexamples

**Difficulty: Blue trail – Easy**

In this tutorial, we will show how Apalache can be used to decide temporal
properties that are more general than invariants.
We will use a simple example specification, modelling a
devious nondeterministic traffic light.

## Specifying temporal properties

The traffic light has two main components: A lamp which can be either red or green,
and a button which can be pushed to request the traffic light to become green.
Consequently, there are two variables:
the current state of the light (either green or red),
and whether the button has been pushed that requests the traffic light to switch from red to green.

The full specification of the traffic light is here:
[TrafficLight.tla](TrafficLight.tla)
But don't worry - we will dissect the spec in the following.

In the TLA specification, this corresponds to
two variables:

```
{{#include TrafficLight.tla:2:15}}
```

Initially, the light should be red and green should not be requested:

```
{{#include TrafficLight.tla:18:20}}
```

We have three possible actions: 
1. The traffic light can switch from red to green, 
2. The traffic light can switch from green to red, or
3. The button can be pushed, thus requesting that the traffic light becomes green.

```
{{#include TrafficLight.tla:actions}}
```

Now, we are ready to specify properties we are interested in.
For example, when green is requested, at some point afterwards the light should actually turn green.
We can write the property like this:

```
{{#include TrafficLight.tla:prop}}
```

Let's run Apalache to check this property:

```
apalache-mc check --temporal=RequestWillBeFulfilled TrafficLight.tla
```
```
...
The outcome is: NoError       
Checker reports no error up to computation length 10
It took me 0 days  0 hours  0 min  2 sec
Total time: 2.276 sec
EXITCODE: OK
```

This is because our traffic watch is actually 
deterministic: 
If it is red and green has not been requested,
the only enabled action is `RequestGreen`.
If it is red and green has been requested,
only `SwitchToGreen` is enabled.
And finally, if the light is green,
only `SwitchToRed` is enabled.

However, we want to make our traffic light more devious.
We will allow the model to stutter, that is,
just let time pass and take no action.

We can write a new next predicate that explicitly allows
stuttering like this:

```
{{#include TrafficLight.tla:stutternext}}
```

Recall that `[Next]_vars` is shorthand for `Next \/ UNCHANGED << vars >>`. Now, let us try to verify the property once again,
using the modified next predicate:

```
apalache-mc check --next=StutteringNext \
    --temporal=RequestWillBeFulfilled TrafficLight.tla
```
```
Step 2: picking a transition out of 3 transition(s)               I@18:04:16.132
State 3: Checking 1 state invariants                              I@18:04:16.150
State 3: Checking 1 state invariants                              I@18:04:16.164
State 3: Checking 1 state invariants                              I@18:04:16.175
State 3: Checking 1 state invariants                              I@18:04:16.186
Check an example state in: /home/user/apalache/docs/src/tutorials/_apalache-out/TrafficLight.tla/2022-05-30T18-04-13_3349613574715319837/counterexample1.tla, /home/user/apalache/docs/src/tutorials/_apalache-out/TrafficLight.tla/2022-05-30T18-04-13_3349613574715319837/MC1.out, /home/user/apalache/docs/src/tutorials/_apalache-out/TrafficLight.tla/2022-05-30T18-04-13_3349613574715319837/counterexample1.json, /home/user/apalache/docs/src/tutorials/_apalache-out/TrafficLight.tla/2022-05-30T18-04-13_3349613574715319837/counterexample1.itf.json E@18:04:16.346
State 3: state invariant 0 violated.                              E@18:04:16.346
Found 1 error(s)                                                  I@18:04:16.347
The outcome is: Error                                             I@18:04:16.353
Checker has found an error                                        I@18:04:16.354
It took me 0 days  0 hours  0 min  2 sec                          I@18:04:16.354
Total time: 2.542 sec                                             I@18:04:16.354
```

This time, we get a counterexample.
Let's take a look at `/home/user/apalache/docs/src/tutorials/_apalache-out/TrafficLight.tla/2022-05-30T18-04-13_3349613574715319837/counterexample1.tla`.

Let's first focus on the initial state.

```
(* Initial state *)
(* State0 ==
  RequestWillBeFulfilled_init = FALSE
    /\ __loop_InLoop = FALSE
    /\ __loop_☐(requestedGreen ⇒ ♢isGreen) = FALSE
    /\ __loop_requestedGreen ⇒ ♢isGreen = TRUE
    /\ __loop_♢isGreen = FALSE
    /\ __loop_isGreen = FALSE
    /\ __loop_requestedGreen = FALSE
    /\ ☐(requestedGreen ⇒ ♢isGreen) = FALSE
    /\ ☐(requestedGreen ⇒ ♢isGreen)_unroll = TRUE
    /\ requestedGreen ⇒ ♢isGreen = TRUE
    /\ ♢isGreen = FALSE
    /\ ♢isGreen_unroll = FALSE
    /\ isGreen = FALSE
    /\ requestedGreen = FALSE *)
State0 ==
  RequestWillBeFulfilled_init = FALSE
    /\ __loop_InLoop = FALSE
    /\ __loop___temporal_t_1 = FALSE
    /\ __loop___temporal_t_2 = TRUE
    /\ __loop___temporal_t_3 = FALSE
    /\ __loop_isGreen = FALSE
    /\ __loop_requestedGreen = FALSE
    /\ __temporal_t_1 = FALSE
    /\ __temporal_t_1_unroll = TRUE
    /\ __temporal_t_2 = TRUE
    /\ __temporal_t_3 = FALSE
    /\ __temporal_t_3_unroll = FALSE
    /\ isGreen = FALSE
    /\ requestedGreen = FALSE
```

Two things are notable:
1. The initial state formula appears twice, once as a comment and once in TLA.
2. There are way more variables than the two variables we specified.

The comment and the TLA specification express the same state, but in the comment, some variable names from the encoding have been replaced
with more human-readable names.
For example, there is a variable called `☐(requestedGreen ⇒ ♢isGreen)` in the comment,
which is called `__temporal_t_1` in TLA.
In the following, let's focus on the content of the comment, since it's easier to understand what's going on.

There are many additional variables in the counterexample because to check temporal formulas, Apalache uses an
encoding that transforms temporal properties to invariants.
If you are interested in the technical details, the encoding is described in sections 3.2 and 4 of [Biere et al.][].
However, to understand the counterexample, you don't need to go into the technical details of the encoding.
We'll go explain the counterexample in the following.

## Counterexamples encode traces with a loop

First, it's important to know that counterexamples to temporal properties are, in general, traces ending in a loop.
A loop is a partial trace that starts and ends with the same state. 
A trace containing a loop describes a possible infinite execution that repeats the loop forever.

For example, what is a trace that is a counterexample to the property `♢isGreen`?
It's an execution that loops without ever finding a state that satisfies `isGreen`.
For example, a counterexample trace might visually look like this:

![A counterexample trace for the property <>isGreen](img/looping_trace.png)

If the execution doesn't loop, then we'd never be sure that there isn't some future state that satisfies `isGreen`.

Apalache can identify looping executions using auxiliary variables.
The auxiliary variable `__loop_InLoop` is true when the trace has started the loop, and false otherwise.
Additionally, when the loop is started, so `__loop_InLoop` switches from true to false,
the current status of variables of the model is stored in an extra copy of those variables.
In our example, it looks like this:
```
(* State0 ==
    ...
    /\ __loop_InLoop = FALSE
    ...
    /\ __loop_isGreen = FALSE
    /\ __loop_requestedGreen = FALSE
    ...
    /\ isGreen = FALSE
    /\ requestedGreen = FALSE *)

(* State1 ==
    ...
    /\ __loop_InLoop = FALSE
    ...
    /\ __loop_isGreen = FALSE
    /\ __loop_requestedGreen = FALSE
    ...
    /\ isGreen = FALSE
    /\ requestedGreen = TRUE *)

(* State2 ==
    ...
    /\ __loop_InLoop = FALSE
    ...
    /\ __loop_isGreen = FALSE
    /\ __loop_requestedGreen = FALSE
    ...
    /\ isGreen = FALSE
    /\ requestedGreen = TRUE *)

(* State3 ==
    ...
    /\ __loop_InLoop = TRUE
    ...
    /\ __loop_isGreen = FALSE
    /\ __loop_requestedGreen = TRUE
    ...
    /\ isGreen = FALSE
    /\ requestedGreen = TRUE *)
```
So, initially, `isGreen` and `requestedGreen` are both false.
Further, `__loop_InLoop` is false, and the copies of `isGreen` and `requestedGreen`, which are called
`__loop_isGreen` and `__loop_requestedGreen`, are equal to the values of `isGreen` and `requestedGreen`.

From state 0 to state 1, `requestedGreen` changes from false to true.
From state 1 to state 2, the system stutters, and nothing seems to change (in fact,
some auxiliary variables 'under the hood' change, which we will dive into later).
Finally, in state 3 `__loop_InLoop` is set to true, which means that
the loop starts in state 2, and the trace from state 3 onward is inside the loop.
However, since state 3 is the last state, this means simply that the trace loops in state 2.
Since the loop starts, the copies of the system variables are also set to the values of the variables in state 2,
so ` __loop_isGreen = FALSE` and `__loop_requestedGreen = TRUE`.


The looping trace in this case can be visualized like this:

![A counterexample trace for the property [](requestedGreen => <>isGreen)](img/counterexample.png)

It is also clear why this trace violates the property:
`requestedGreen` holds in state 1, but `isGreen` never holds,
so in state 1 the property `requestedGreen => <>isGreen` is violated.

## Auxiliary variables encode evaluations of subformulas along the trace

Next, let us discuss the other auxiliary variables that are introduced by Apalache to check the temporal property.
These extra variables correspond to parts of the temporal property we want to check.
These are the following variables with their valuations in state 0:

```
(* State0 ==
  RequestWillBeFulfilled_init = FALSE
    ...
    /\ ☐(requestedGreen ⇒ ♢isGreen) = FALSE
    /\ ☐(requestedGreen ⇒ ♢isGreen)_unroll = TRUE
    /\ requestedGreen ⇒ ♢isGreen = TRUE
    /\ ♢isGreen = FALSE
    /\ ♢isGreen_unroll = FALSE
    ...
```
There are three groups of variables: those that look like formulas, e.g. `☐(requestedGreen ⇒ ♢isGreen)`,
those that look like formulas and end with `_unroll`,
e.g., and the variable `RequestWillBeFulfilled_init`.

Let's focus on the non-`_unroll` variables that look like formulas
first.

Recall that the temporal property we want to check is `[](requestedGreen => <>isGreen)`.
That's also the name of one of the variables: The value of the variable 
`☐(requestedGreen ⇒ ♢isGreen)` tells us whether starting in the current state, the
formula `[](requestedGreen => <>isGreen)` holds. Since we are looking at a counterexample, it is not
surprising that the formula does not hold in state 0.

Similarly, the variable `requestedGreen ⇒ ♢isGreen` tells us whether
the property `requestedGreen ⇒ ♢isGreen` holds at the current state.
It might be surprising to see that the property holds
but recall that in state 0, `requestedGreen = FALSE`, so the implication is satisfied.
Finally, we have the variable `♢isGreen`, which is false, telling
us that along the execution, `isGreen` will never be true.

You might already have noticed the pattern of which formulas appear as variables.
Take our property `[](requestedGreen => <>isGreen)`.
The syntax tree of this formula looks like this:

![The syntax tree for the formula [](requestedGreen => <>isGreen)](img/syntaxtree.png)

For each node of the syntax tree where the formula contains a temporal operator,
there is an auxiliary variable. And as mentioned before, the value of 
the variable in a state tells us whether from that state, the subformula is true. In this particular example, the formulas that correspond to variables in the encoding are filled with orange in the syntax tree.

What about the `_unroll` variables? There is one `_unroll` variable for each temporal operator in the formula.
For example, `☐(requestedGreen ⇒ ♢isGreen)_unroll` is the unroll-variable for the
leading box operator. These are necessary because to know whether a formula like
`[]isGreen` holds in the last state of the loop, we need to know whether
`isGreen` holds in all states of the loop. However, when we are in the last state of the loop,
we won't see the state of the loop again! So we need to store this information when we traverse the loop.
That's why we have an extra variable, which essentially tells us whether `isGreen` holds on all states of the loop.
Let us take a look at the valuations of `☐(requestedGreen ⇒ ♢isGreen)_unroll` along the execution to see this.

```
(* State0 ==
    ...
    /\ __loop_InLoop = FALSE
    ...
    /\ ☐(requestedGreen ⇒ ♢isGreen) = FALSE
    /\ ☐(requestedGreen ⇒ ♢isGreen)_unroll = TRUE
    ...

(* State1 ==
    ...
    /\ __loop_InLoop = FALSE
    ...
    /\ ☐(requestedGreen ⇒ ♢isGreen) = FALSE
    /\ ☐(requestedGreen ⇒ ♢isGreen)_unroll = TRUE
    ...

(* State2 ==
    ...
    /\ __loop_InLoop = FALSE
    ...
    /\ ☐(requestedGreen ⇒ ♢isGreen) = FALSE
    /\ ☐(requestedGreen ⇒ ♢isGreen)_unroll = TRUE
    ...

(* State3 ==
    ...
    /\ __loop_InLoop = TRUE
    ...
    /\ ☐(requestedGreen ⇒ ♢isGreen) = FALSE
    /\ ☐(requestedGreen ⇒ ♢isGreen)_unroll = FALSE
    ...
```

So in the last state, `☐(requestedGreen ⇒ ♢isGreen)_unroll`
is not true, since `☐(requestedGreen ⇒ ♢isGreen)`
does not hold in state 2, which is on the loop.

Notice that for the variables corresponding to nodes in the
syntax tree, e.g. `☐(requestedGreen ⇒ ♢isGreen)`,
we have loop copies, e.g. `__loop_☐(requestedGreen ⇒ ♢isGreen)`.



These fulfill the same function as the `__loop_` copies for the
original variables of the model, as explained above.

```
(* State0 ==
    ...
    /\ __loop_☐(requestedGreen ⇒ ♢isGreen) = FALSE
    /\ __loop_requestedGreen ⇒ ♢isGreen = TRUE
    /\ __loop_♢isGreen = FALSE
    /\ __loop_isGreen = FALSE
    /\ __loop_requestedGreen = FALSE
```

Finally, let's discuss `RequestWillBeFulfilled_init`.
Recall that the variables for subformulas store
the evaluations of the subformulas at the current point in the execution.
This means that when we are at the end of the execution, we don't know
whether the variable for the whole formula, e.g. `☐(requestedGreen ⇒ ♢isGreen)`, was true in the first state.
That's what `RequestWillBeFulfilled_init` is for:
it tells us whether in the first state of the execution, our temporal
property holds true
(recall that we named the property "RequestWillBeFulfilled").

## Further reading

In this tutorial, we learned how to specify temporal properties
in Apalache, and how to read counterexamples for such properties.

If you want to dive deeper into the
encoding, it is formally explained in sections 3.2 and 4 of
[Biere et al.]. To understand why this encoding was chosen,
you can read the [ADR on temporal properties].
Finally, if you want to go into the nitty-gritty details and see
the encoding in action,
you can look at the intermediate TLA specifying the encoding.

Run

```
apalache-mc check --next=StutteringNext \
    --write-intermediate=yes --temporal=RequestWillBeFulfilled TrafficLight.tla
```

You will get intermediate output in a folder named like
`_apalache_out/TrafficLight/TIMESTAMP/intermediate/`.
There, take a look at `0X_OutTemporalPass.tla`.


[Biere et al.]: https://lmcs.episciences.org/2236
[ADR on temporal properties]: ../adr/017pdr-temporal.md
