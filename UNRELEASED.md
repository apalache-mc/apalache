<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Feature Category 1

         * Change description, see #123

        ### Feature Category 2

         * Another change description, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Bug fixes

 * handling big integers, see #450
 * expanding tuples in quantifiers, see #476
 * unfolding UNCHANGED for arbitrary expressions, see #471
 * unfolding UNCHANGED <<>>, see #475

### Features

 * constant simplification over strings, see #197
 * propagation of primes inside expressions,
   e.g., (f[i])' becomes f'[i'] if both f and i are state variables

