## 0.8.4

### Feature Model Checker

 * new sequential model checker that is using TransitionExecutor, see #467
 * new command-line options, see #467 and the manual for details:
   - choose the algorithm: `--algo=(offline|incremental)`
   - pre-check, whether a transition disabled, discard the disabled transitions: `--discard-disabled`
   - do not check for deadlocks: `--no-deadlock`
   - pass tuning parameters in CLI: `--tune-here`

### Feature TLA+ Parser (SANY importer)

  * parsing in-comment Java-like annotations, see #226
  * tracking the source of variable/constant declarations and operator definitions, see #262

### Bugfixes

 * the new sequential model checker has uncovered a bug that was not found
   by the old model checker, see #467

### Documentation

  * ADR004: In-comment annotations for declarations (of constants, variables, operators)
