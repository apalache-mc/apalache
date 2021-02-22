## 0.10.1

### Features

* Support for `FunAsSeq` conversion in the type checker, see #223
* The parser outputs annotations, see #502

### Documentation

* HOWTO on writing type annotations, see #571

### Bug fixes

* Fixed name collisions on LOCAL operators and LOCAL INSTANCE, see #576
* Parser: a higher-order operator calling a higher-order operator, see #575
* Type checker: support for recursive functions of multiple arguments, see #582
* Type checker: support for tuple unpacking in recursive functions, see #583
