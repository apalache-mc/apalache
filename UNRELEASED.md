<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Breaking changes

 * Recommended JDK version was bumped to JDK17, see #1662
 * Add the option `--features` to enable experimental features, see #1648
 * Never report a deadlock when `--no-deadlock=1`, see #1679

### Features

* Add the option `--features` to enable experimental features, see #1648
* Never load TLC config files by default, see #1676
* Experimental type unification over rows, new records, and variants, see #1646

### Bug fixes

* Fix references to `--tune-here` (actually `--tuning-options`), see #1579
* Not failing when assignment and `UNCHANGED` appear in invariants, see #1664