## 0.15.3

### Features

* Checker: Support for CASE without OTHER, see #285

### Bug fixes
* Type checker: Showing an error on missing annotations CONSTANTs or VARIABLEs, see #705

### Changed

* IR: simplified `SimpleFormalParam` and `OperFormalParam` into `OperParam`, see #656
* IR: made consistent the names of IR operators (may break JSON compatibility), see #634
