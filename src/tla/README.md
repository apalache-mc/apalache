# Apalache's Custom TLA Modules

The TLA modules in this directory are made available to SANY when parsing. This
is achieved in the package distribution by copy all `*.tla` files from this
directory into `tla2snay/StandardModules` when assembling the fat JAR. 

See the `assembly` settings in the [../../build.sbt](../../build.sbt)'s `root`
project for the implementation.
