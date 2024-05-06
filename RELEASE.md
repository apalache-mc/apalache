## 0.44.11 - 2024-05-06

### Features

- TLA+ modules produced by the Shai command `TLA` now include type annotations (#2891)

### Bug fixes

- Fixed a problem where folds produced by the Shai command `TLA` had an invalid form and could not be parsed back (#2891)
- Fixed a problem where bindings from exists and forall operators where not properly sanitized before printing (#2891)
- Fixed a problem where translation from `slice` to `replaceAt` added an incorrect increment to the last argument (#2891)
