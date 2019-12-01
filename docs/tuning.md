Parameters for fine tuning
==========================

The parameters for fine tuning can be passed to the checker in a properties file.
Its name is given with the command-line option ``--tuning=my.properties.`` This file
supports variable substitution, e.g., ``${x}`` is replaced with the value of ``x``, if it was
previously declared.
 

1. __Timeouts__: ``search.transition.timeout=<seconds>`` and ``search.invariant.timeout=<seconds>`` set timeouts
  in seconds for checking whether a transition is enabled and whether the invariant holds, respectively.
  When a timeout occurs, while transition is checked, the transition is considered disabled
  and the search continues. When a timeout occurs, while the invariant is checked, the invariant
  is considered satisfied. Obviously, one can miss a bug by setting small timeouts.
  
1. __Guided search__: ``search.transitionFilter=<sequence>``. Restrict the choice of symbolic
  transitions at every step with a regular expression. For instance, ``search.filter=0,5,2|3``
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
  
1. __Invariant checking by splitting__: `search.invariant.split=(false|true)`. If the option
is set to true, the invariant is checked individually for every enabled transition. Otherwise,
the invariant is checked once after all enabled transitions have been added into the SMT context.
By default, `search.invariant.split=true`
  
1. __Learning from invariants__: ``search.invariant.learnFromUnsat=(false|true)``. If the option
is set to true, once the checked found that `~Inv` does not hold for some depth, it adds the
assumption `Inv` in the SMT context. 
   
1. __Randomized search__: ``search.randomDfs=(false|true)``. When the symbolic transitions
  are enumerated in the depth-first order, that is, ``search=dfs``, choose the next transition
  randomly.
  
1. __Translation to SMT__:
  
  1. __Short circuiting__: `rewriter.shortCircuit=(false|true)`. When `rewriter.shortCircuit=true`, `A \/ B` and `A /\ B` are translated to SMT as if-then-else expressions, e.g., `(ite A true B)`. Otherwise, disjunctions and conjunctions are directly translated to `(or ...)` and `(and ...)` respectively. By default, `rewriter.shortCircuit=false`.

  1. __Lazy short circuiting__: `rewriter.lazyCircuit=(false|true)`. Given `A /\ B`, first check with the solver, whether `A` is satisfiable. If not, return reduce to `false` immediately; otherwise, rewrite `B`. By default, `rewriter.lazyCircuit=false`.
