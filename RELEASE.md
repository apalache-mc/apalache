## 0.40.4 - 2023-06-23

### Bug fixes

- Fixed a bug in pointer propagation, where sets cherrypicked from a powerset would always have the exact same pointers as the base set, instead of some subset thereof (though SMT constraints were added correctly). This broke counterexample reconstruction. See #2606
- Fix translation of nested/shadowed "_" Quint lambda parameters, see #2608
