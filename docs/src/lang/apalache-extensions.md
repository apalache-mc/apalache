# Apalache extensions

Apalache provides the user with several TLA+ modules. These modules introduce
TLA+ operators to allow for more efficient model checking with Apalache. Since
our users may run Apalache and TLC interchangeably, the modules contain
default definitions in TLA+ that are compatible with TLC. Apalache overrides
these definitions internally for more efficient treatment compared to the default TLA+
definitions.

Currently supported modules:

 - [Apalache module](./apalache-operators.md)
 - [Variants](./variants.md)
 - [Option Types](./option-types.md)
