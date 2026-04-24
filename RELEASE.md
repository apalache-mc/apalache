## 0.57.0 - 2026-04-24

### Features

- Honor TLC's `CHECK_DEADLOCK` config keyword: `CHECK_DEADLOCK FALSE` now behaves like `--no-deadlock` and `CHECK_DEADLOCK TRUE` preserves the default deadlock-checking behavior. The CLI flag `--no-deadlock` (and `apalache.cfg`) still takes precedence over the value from the TLC config file (#3311).
