## 0.57.1 - 2026-05-22

### Breaking changes

- Upgrade the TLA+ parser to SANY 1.8.0 and add Unicode support, may change parsing behavior and diagnostics #3341
- Bump Scala to 2.13.18

### Features

- Extend set simplification rules to handle previously missing cases (#3343)

### Bug fixes

- Fixed a SANY importer crash when a named ASSUME definition is used as an operator, see #3318.
- Fixed a preprocessing failure when a named ASSUME declaration is referenced from an operator body, see #3326.
