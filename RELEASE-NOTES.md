## 0.24.0

### Breaking changes
* `RECURSIVE` operators and functions are no longer supported, see #1569
* rename Apalache `FoldSet` and `FoldSeq` to `ApaFoldSet` and `ApaFoldSeqLeft`, see #1617

### Features

* Add the operator `Apalache!Guess`, see #1590 and #888
* Extend the type parser to support ADR014 (experimental), see #1602
* Keramelizer now rewrites \subseteq using forall quantification, see #1408
* Builtin operators can be passed as arguments to HO operators, see #1630
* Optimize set membership for record sets, see #1629