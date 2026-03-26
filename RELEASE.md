## 0.56.1 - 2026-03-26

### Features

- Add support for the `leadsTo` operator when translating Quint to TLA+

### Bug fixes

- Fix TLA+ printers to wrap LET-IN expressions in parentheses when nested inside another expression, preventing unintended scope extension through `/\` conjuncts
- Fix "used before it is assigned" error when using grouped-variable UNCHANGED with nested operator references (e.g., `vars == <<myList1, myList2>>` where `myList1 == <<myVar1, myVar2>>`), see #3143
