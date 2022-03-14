## 0.22.2

### Features
 * Enable records in the arrays encoding, see #1288
 * Enable the remaining TLA+ features in the arrays encoding, see #1418
 * Implement the sequence constructor `Apalache!MkSeq`, see #1439
 * Add support for `Apalache!FunAsSeq`, see #1442
 * Implement `EXCEPT` on sequences, see #1444
 * Cache default values, see #1465

### Bug fixes
 * Fixed bug where TLA+ `LAMBDA`s wouldn't inline outside `Fold` and `MkSeq`, see #1446
 * Fix the comment preprocessor to extract annotations after a linefeed, see #1456
 * Fix the failing property-based test, see #1454
 * Fixed a bug where call-by-name embedding wasn't properly called recursively 
