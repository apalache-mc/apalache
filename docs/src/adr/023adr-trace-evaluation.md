# ADR-023: Trace evaluation

| authors                                | last revised    |
| -------------------------------------- | --------------: |
| Jure Kukovec                           | 2022-09-28      |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

<!-- Statement to summarize, following the following formula: -->

In the context of improving usability\
facing difficulties understanding counterexample traces\
we decided to implement trace evaluation\
to achieve a better user experience\
accepting the development costs.

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->
As explained in [#1845](https://github.com/informalsystems/apalache/issues/1845), one often runs into the problem of unreadable counterexamples; 
for complex specifications, it is often the case that either the state contains many variables, or the invariant contains many conjunctive components (or both).
In that case, trying to determine exactly why e.g. `A1 /\ ... /\ An` was violated basically boils down to manually evaluating each formula `Ai` with whatever variables are present in the state.
This is laborious and error-prone, and should be automated.


## Options

<!-- Communicate the options considered.
     This records evidence of our circumspection and documents the various alternatives
     considered but not adopted.
-->
1. Call REPL in each state:
    - No convenient REPL integration at the moment
    - No clear way of saving outputs
1. Encode trace traversal as an Apalache problem and use the solver
    - No additional rules or IO needed

## Solution

<!-- Communicates what solution was decided, and it is expected to solve the
     problem. -->

We choose option (2). 

Suppose we are given a trace `s_0 -> s_1 -> ... -> s_n` over variables `x_1,...,x_k` as well as expressions `E_1,...,E_m`, such that all free variables of `E_1,...,E_m` are among `x_1,...,x_k`. W.l.o.g. assume all constants are inlined.

The above defines a trace `t_0 -> t_1 -> ... -> t_n` over variables `v_1,...,v_m`, such that 
```
t_i.v_j = E_j[s_i.x_1/x_1,...,s_i.x_k/x_k]
```

for all `i \in 0..n, j \in 1..m`. In other words, `v_j` in state `t_i` is the evaluation of the expression `E_j` in state `s_i`.

By using transition filtering instead of a generic Next-decomposition, this can be encoded as a specification free of control-nondeterminism, in-state computation, or invariants, and is thus incredibly efficient to represent in SMT.

Then, the solver will naturally return an ITF trace containing the evaluations of `E_1,...,E_m` in each state `s_0,...,s_n` (the values of `v_1,...,v_m`).

## Input

The invocation of the trace evaluation command should look like this:
```sh
$ apalache-mc tracee --trace=<trace> --expressions=<exprs> <source>
```
where:
  - `<trace>` is a trace produced by apalache, in either `.tla`, `.json` or `.itf.json` formats
  - `<exprs>` is a comma-separated list of expression names, to be evaluated over the trace provided by `--trace`
  - <source> is a valid apalache input source (`.tla` or `.json`), containing a specification over the same variables as the trace, with all of the expressions provided by `--expressions` as operator declarations

Note that `<source>` can just be the file used to produce the trace in the first place.

## Output

The above command should produce an Apalache trace (in all available formats), with the following properties:
  - The output trace length is equal to the input trace length
  - If `--expressions=E_1,...,E_m` is used, the variables of the output trace are `E_1,...,E_m`.
  - For all `i,j`, the value of `E_i` in state `j` of the output trace is equal to the evaluation of `E_i`, as defined in `<source>`, using the values the variables of the input trace hold in state `j` of the input trace.

Recall that the output trace will only display the expressions `E_1,...E_m` as the output state variables. Should you wish to view the original trace variables, you need to add an expression, like one of the ones below for example:
```tla
E_single == x_1
E_state == [ x1 |-> x_1, ..., xk |-> x_k ]
E_vars == <<x_1, ..., x_k>>
```


Optionally, we could investigate one of the following two alternatives to the output format:
  1. The output trace variables are `x_1,...,x_k,E_1,...,E_m` instead, where `x_1,...,x_k` are the variables of the original trace. The value of each variable from the input trace has the same value in every state of the output trace, as it does in the corresponding state of the input trace.
  This is perhaps preferable to use with the [ITF trace viewer](https://github.com/informalsystems/vscode-itf-trace-viewer).
  2. The output contains _both_ the input trace and the output trace (as it would have been produced in the original suggestion) in the same file, but separately.


## Example

Assume we are given the source `test.tla`
<details>
<summary>Source</summary>

```tla
-------------------------- MODULE test -----------------------------

EXTENDS Integers

VARIABLE
  \* @type: Int;
  x

A == x * x
B == IF x < 3 THEN 0 ELSE 1
C == [y \in {1,2,4} |-> {y} ][x]
D == x % 2 = 0

Init == x = 1
Next == x' = x + 1

Inv == TRUE
  

=========================================================================
```
</details>

and trace `testTrace.json` (length 5, `x=1 -> ... -> x=5`).
<details>
<summary>Trace</summary>

```json
{
  "name": "ApalacheIR",
  "version": "1.0",
  "description": "https://apalache.informal.systems/docs/adr/005adr-json.html",
  "modules": [
    {
      "kind": "TlaModule",
      "name": "counterexample",
      "declarations": [
        {
          "type": "() => Bool",
          "kind": "TlaOperDecl",
          "name": "ConstInit",
          "formalParams": [
            
          ],
          "isRecursive": false,
          "body": {
            "type": "Untyped",
            "kind": "ValEx",
            "value": {
              "kind": "TlaBool",
              "value": true
            }
          }
        },
        {
          "type": "() => Bool",
          "kind": "TlaOperDecl",
          "name": "State0",
          "formalParams": [
            
          ],
          "isRecursive": false,
          "body": {
            "type": "Bool",
            "kind": "OperEx",
            "oper": "AND",
            "args": [
              {
                "type": "Bool",
                "kind": "OperEx",
                "oper": "EQ",
                "args": [
                  {
                    "type": "Int",
                    "kind": "NameEx",
                    "name": "x"
                  },
                  {
                    "type": "Int",
                    "kind": "ValEx",
                    "value": {
                      "kind": "TlaInt",
                      "value": 1
                    }
                  }
                ]
              }
            ]
          }
        },
        {
          "type": "() => Bool",
          "kind": "TlaOperDecl",
          "name": "State1",
          "formalParams": [
            
          ],
          "isRecursive": false,
          "body": {
            "type": "Bool",
            "kind": "OperEx",
            "oper": "AND",
            "args": [
              {
                "type": "Bool",
                "kind": "OperEx",
                "oper": "EQ",
                "args": [
                  {
                    "type": "Int",
                    "kind": "NameEx",
                    "name": "x"
                  },
                  {
                    "type": "Int",
                    "kind": "ValEx",
                    "value": {
                      "kind": "TlaInt",
                      "value": 2
                    }
                  }
                ]
              }
            ]
          }
        },
        {
          "type": "() => Bool",
          "kind": "TlaOperDecl",
          "name": "State2",
          "formalParams": [
            
          ],
          "isRecursive": false,
          "body": {
            "type": "Bool",
            "kind": "OperEx",
            "oper": "AND",
            "args": [
              {
                "type": "Bool",
                "kind": "OperEx",
                "oper": "EQ",
                "args": [
                  {
                    "type": "Int",
                    "kind": "NameEx",
                    "name": "x"
                  },
                  {
                    "type": "Int",
                    "kind": "ValEx",
                    "value": {
                      "kind": "TlaInt",
                      "value": 3
                    }
                  }
                ]
              }
            ]
          }
        },
        {
          "type": "() => Bool",
          "kind": "TlaOperDecl",
          "name": "State3",
          "formalParams": [
            
          ],
          "isRecursive": false,
          "body": {
            "type": "Bool",
            "kind": "OperEx",
            "oper": "AND",
            "args": [
              {
                "type": "Bool",
                "kind": "OperEx",
                "oper": "EQ",
                "args": [
                  {
                    "type": "Int",
                    "kind": "NameEx",
                    "name": "x"
                  },
                  {
                    "type": "Int",
                    "kind": "ValEx",
                    "value": {
                      "kind": "TlaInt",
                      "value": 4
                    }
                  }
                ]
              }
            ]
          }
        },
        {
          "type": "() => Bool",
          "kind": "TlaOperDecl",
          "name": "State4",
          "formalParams": [
            
          ],
          "isRecursive": false,
          "body": {
            "type": "Bool",
            "kind": "OperEx",
            "oper": "AND",
            "args": [
              {
                "type": "Bool",
                "kind": "OperEx",
                "oper": "EQ",
                "args": [
                  {
                    "type": "Int",
                    "kind": "NameEx",
                    "name": "x"
                  },
                  {
                    "type": "Int",
                    "kind": "ValEx",
                    "value": {
                      "kind": "TlaInt",
                      "value": 5
                    }
                  }
                ]
              }
            ]
          }
        },
        {
          "type": "() => Bool",
          "kind": "TlaOperDecl",
          "name": "InvariantViolation",
          "formalParams": [
            
          ],
          "isRecursive": false,
          "body": {
            "type": "Bool",
            "kind": "ValEx",
            "value": {
              "kind": "TlaBool",
              "value": true
            }
          }
        }
      ]
    }
  ]
}
```

</details>

After running `tracee --trace=testTrace.json --expressions=A,B,C,D test.tla`, we should see
```
...
Constructing an example run                                       I@16:06:59.450
Check the trace in: <PATH>/example0.tla, ... I@16:06:59.563
The outcome is: NoError                                           I@16:06:59.571
Trace successfully generated.   
```

where `example0.tla` looks like

<details>
<summary>Result</summary>

```tla
---------------------------- MODULE counterexample ----------------------------

EXTENDS test

(* Constant initialization state *)
ConstInit == TRUE

(* Initial state *)
State0 == A = 1/\ B = 0/\ C = {1}/\ D = FALSE

(* Transition 0 to State1 *)
State1 == A = 4/\ B = 0/\ C = {2}/\ D = TRUE

(* Transition 1 to State2 *)
State2 == A = 9/\ B = 1/\ C = {}/\ D = FALSE

(* Transition 2 to State3 *)
State3 == A = 16/\ B = 1/\ C = {4}/\ D = TRUE

(* Transition 3 to State4 *)
State4 == A = 25/\ B = 1/\ C = {}/\ D = FALSE

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == TRUE

================================================================================
(* Created by Apalache on Mon Oct 17 16:06:59 CEST 2022 *)
(* https://github.com/informalsystems/apalache *)
```

</details> 

## Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

TBD
