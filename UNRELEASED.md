<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Feature Category 1

         * Change description, see #123

        ### Feature Category 2

         * Another change description, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Features

 * handling big integers, #450
 * new sequential model checker that is using TransitionExecutor, see #467
 * new command-line options, see #467 and the manual for details:
   - choose the algorithm: `--algo=(offline|incremental)`
   - pre-check, whether a transition disabled, discard the disabled transitions: `--discard-disabled`
   - do not check for deadlocks: `--no-deadlock`
   - pass tuning parameters in CLI: `--tune-here`
 * constant simplification over strings, #197

### Bugfixes

 * the new sequential model checker has uncovered a bug that was not found
   by the old model checker, , see #467
