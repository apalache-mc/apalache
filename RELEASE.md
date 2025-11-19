## 0.52.0 - 2025-11-19

### Features

- Add the method `assumeState` of JSON RPC
- Add the missing case of deserializing variants from ITF JSON (#3215)

### Bug fixes

- Fix resulting snapshots in `assumeTransition` and `assumeState` (#3219)
- Fix the ITF deserializer to use the modern record types (#3216)
