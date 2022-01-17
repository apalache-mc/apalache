## 0.19.2

### Design

 * ADR-014 on precise type checking for records and variants, see #1151

### Features

 * Output in the Informal Trace Format, see #1220

### Bug fixes

 * Add constant simplification rules that may improve performance in specific scenarios, see #1206
 * Fix expansion of `~` in configured paths, see #1208
 * Fix a bug where an implication with its left side simplified to the `TRUE` constant was incorrectly translated, see #1206
