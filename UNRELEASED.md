<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->

### Features

* New errors for the following constant simplification scenarios (see #1191):
  1. Division by 0
  1. Mod (%) by 0
  1. Negative expoents
  1. Expoents bigger than an Integer
  1. Expoential operations that would overflow `BigInt`

### Bug Fixes
