## 0.24.2

### Breaking changes

 * Recommended JDK version was bumped to JDK17, see #1662
 * Add the option `--features` to enable experimental features, see #1648
 * Never report a deadlock when `--no-deadlock=1`, see #1679

### Features

* Include the version number in `detailed.log`, see #1678
* Add the option `--features` to enable experimental features, see #1648
* Never load TLC config files by default, see #1676
* Experimental type unification over rows, new records, and variants, see #1646
* Experimental type checking for records over rows, see #1688

### Bug fixes

* Fix references to `--tune-here` (actually `--tuning-options`), see #1579
* Not failing when assignment and `UNCHANGED` appear in invariants, see #1664
