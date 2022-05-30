# Temporal properties and counterexamples

**Difficulty: Blue trail – Easy**

In this tutorial, we will show how Apalache can be used to decide temporal
properties that are more general than invariants.
We will use a simple example specification, modelling a
devious nondeterministic traffic light.

The traffic light has two main components: A lamp which can be either red or green,
and a button which can be pushed to request the traffic light to become green.
Consequently, there are two variables:
the current state of the light (either green or red),
and whether the button has been pushed that requests the traffic light to switch from red to green.
In the TLA specification, this corresponds to
two variables:

```
{{#include TrafficLight.tla:3:15}}
```

Initially, the light should be red and green should not be requested:

```
{{#include TrafficLight.tla:7:20}}
```

We have three possible actions: 
1. The traffic light can switch from red to green, 
2. The traffic light can switch from green to red, or
3. The button can be pushed, thus requesting that the traffic light becomes green.

```
{{#include TrafficLight.tla:22:58}}
```

Now, we are ready to specify properties we are interested in.
For example, when green is requested, at some point afterwards the light should actually turn green.
We wan write the property like this:

```
{{#include TrafficLight.tla:60:61}}
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

However, we want to make our traffic light more devious,
so we will allow the model to stutter, that is,
just let time pass and take no action.

We can write a new next predicate that explicitly allows
stuttering like this:

```
{{#include TrafficLight.tla:63:64}}
```

Recall that `[Next]_vars` is shorthand for `Next \/ UNCHANGED << vars >>`. Now, let us try to verify the property once again:

```
apalache-mc check --next=StutteringNext --temporal=RequestWillBeFulfilled TrafficLight.tla
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
Let's take a look at `/home/user/apalache/docs/src/tutorials/_apalache-out/TrafficLight.tla/2022-05-30T18-04-13_3349613574715319837/counterexample1.tla`:

```

```

