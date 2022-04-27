<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Features

* Experimental type unification over rows, new records, and variants, see #1646

### Breaking changes

* Add the option `--features` to enable experimental features, see #1648
* Never load TLC config files by default, see #1676

### Bug fixes

* Fix references to `--tune-here` (actually `--tuning-options`), see #1579
* Not failing when assignment and `UNCHANGED` appear in invariants, see #1664
