# Five minutes of theory

**You can safely skip this section**

Given a TLA+ specification, with all parameters fixed, our model checker
performs the following steps:

 1. It automatically extracts symbolic transitions from the specification. This
 allows us to partition the action `Next` into a disjunction of simpler actions
 `A_1, ..., A_n`.

 2. Apalache translates operators `Init` and `A_1, ..., A_n` to SMT formulas.
 This allows us to explore bounded executions with an SMT solver (we are using
 [Microsoft's Z3](https://github.com/Z3Prover/z3)). For instance, a sequence of
 `k` steps `s_0, s_1, ..., s_k`, all of which execute action `A_1`, is encoded
 as a formula `Run(k)` that looks as follows:

```tla
[[Init(s_0)]] /\ [[A_1(s_0, s_1)]] /\ ... /\ [[A_1(s_(k-1), s_k)]]
```

To find an execution of length `k` that violates an invariant `Inv`, the tool
adds the following constraint to the formula `Run(k)`:

```tla
[[~Inv(s_0)]] \/ ... \/ [[~Inv(s_k)]]
```

Here, `[[_]]` is the translator from TLA+ to SMT. Importantly, the values for
the states `s_0`, ..., `s_k` are not enumerated as in TLC, but have to be found
by the SMT solver.

If you would like to learn more about theory behind Apalache, check the [paper
delivered at OOPSLA19](https://dl.acm.org/doi/10.1145/3360549).
