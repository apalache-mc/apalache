## 0.8.2

### Bug fixes

 * handling big integers, see #450
 * better parsing of SPECIFICATION in TLC configs, see #468
 * expanding tuples in quantifiers, see #476
 * unfolding UNCHANGED for arbitrary expressions, see #471
 * unfolding UNCHANGED <<>>, see #475

### Features

 * constant simplification over strings, see #197
 * propagation of primes inside expressions,
   e.g., (f[i])' becomes f'[i'] if both f and i are state variables
