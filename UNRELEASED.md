<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->

### Features

* New errors for the following constant simplification scenarios (see #1191):
  a. Division by 0
  b. Mod (%) by 0
  c. Negative expoents
  d. Expoents bigger than an Integer
  e. Expoential operations that would overflow `BigInt`

### Bug Fixes
