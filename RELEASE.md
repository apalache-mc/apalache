## 0.25.6 - 2022-06-06

### Features

- Always output an example trace, add `--save-runs` flag to save examples for each run of `simulate`, see #1838

### Bug fixes

- Output rare expressions as unserializable to ITF, see #1841
- Fix a problem in comparing functions with empty domains in the arrays encoding, see #1811
- Fix spurious counter-example generation with functions of records in the arrays encoding, see #1840
