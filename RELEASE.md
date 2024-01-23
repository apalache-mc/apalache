## 0.44.3 - 2024-01-23

### Features

- Parse name of `ASSUME` declarations into IR and preserve them during serialization to JSON, see #2808

### Bug fixes

- fix crash on the arrays encoding when having a subset relation containing infinite sets, see #2810
