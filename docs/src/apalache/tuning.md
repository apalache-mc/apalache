Parameters for fine tuning
==========================

The parameters for fine tuning can be passed to the checker in a properties
file.  Its name is given with the command-line option `--tuning=my.properties.`
This file supports variable substitution, e.g., `${x}` is replaced with the
value of `x`, if it was previously declared.

Alternatively, you can pass the tuning options right in the command-line by
passing the option `--tune-here` that has the following format:
    
    ```
    --tune-here=key1=val1
    --tune-here=key1=val1:key2=val2
    ...
    ```

1. __Randomization__: `smt.randomSeed=<int>` passes the random seed to `z3` (via
  `z3`'s parameters `sat.random_seed` and `smt.random_seed`). 

1. __Timeouts__: ``search.smt.timeout=<seconds>`` defines the timeout to the SMT solver
  in seconds. The default value is `0`, which stands for the unbounded timeout.
  For instance, the timeout is used in the following cases:
  checking if a transition is enabled, checking an invariant, checking for deadlocks.
  If the solver times out, it reports 'UNKNOWN', and the model checker reports a runtime
  error.

1. __Guided search__: ``search.transitionFilter=<regex>``.
  Restrict the choice of symbolic transitions at every step with a regular expression.
  The regular expression should recognize words over of the form 's->t', where `s`
  is a regular expression over step numbers and `t` is a regular expression over
  transition numbers. For instance,
  `search.transitionFilter=(0->0|1->5|2->2|3->3|[4-9]->.*|[1-9][0-9]+->.*)`
  requires to start with the 0th transition, continue with the 5th transition,
  then execute either the 2nd or the 3rd transition and after that execute
  arbitrary transitions until the ``length.`` Note that there is no direct correspondence
  between the transition numbers and the actions in the TLA+ spec. Check the 
  transition numbers in `./x/**/out-transition.tla`: 0th transition is called `Next$0`, 1st transition is called `Next$1`, etc.
  
1. __Invariant checking at certain steps__: ``search.invariantFilter=regex``.
  Check the invariant only at the steps that satisfy the regular expression.
  For instance, ``search.invariantFilter=10|15|20`` tells the model checker to
  check the invariant only *after* exactly 10, 15, or 20 step were made. Step 0 corresponds
  to the initialization with ``Init``, step 1 is the first step with ``Next``, etc.
  This option is useful for checking consensus algorithms, where the decision
  cannot be revoked. So instead of checking the invariant after each step, we can
  do that after the algorithm has made a good number of steps. 
  
1. __Translation to SMT__:
  
  1. __Short circuiting__: `rewriter.shortCircuit=(false|true)`. When `rewriter.shortCircuit=true`, `A \/ B` and `A /\ B` are translated to SMT as if-then-else expressions, e.g., `(ite A true B)`. Otherwise, disjunctions and conjunctions are directly translated to `(or ...)` and `(and ...)` respectively. By default, `rewriter.shortCircuit=false`.

  1. __Lazy short circuiting__: `rewriter.lazyCircuit=(false|true)`. Given `A /\ B`, first check with the solver, whether `A` is satisfiable. If not, return reduce to `false` immediately; otherwise, rewrite `B`. By default, `rewriter.lazyCircuit=false`.
