# Apalache extensions

Apalache provides the user with several TLA+ modules. These modules introduce
TLA+ operators to allow for more efficient model checking with Apalache. Since
our users may run Apalache and TLC interchangeably, the modules contain the
default definitions that are compatible with TLC. Apalache treats the operators
defined in these modules more efficiently than if it was using the default
definitions.

Currently supported modules:

 - [Apalache module](./apalache-operators.md)
 - [Variants](./variants.md)

