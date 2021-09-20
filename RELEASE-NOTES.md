## 0.16.1

### Bug fixes

 * Fixed a heisenbug caused by EXCEPT on records, which used unsorted keys, see #987
 * Fixed unsound skolemization that applied to let-definitions, see #985
