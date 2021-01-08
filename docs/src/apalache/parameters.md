# Setting up specification parameters

Similar to TLC, Apalache requires the specification parameters to be restricted
to finite values. In contrast to TLC, there is a way to initialize parameters
by writing a symbolic constraint, see [Section 5.3](#ConstInit).

## Using INSTANCE

You can set the specification parameters, using the standard `INSTANCE`
expression of TLA+. For instance, below is the example
[`y2k_instance.tla`](https://github.com/informalsystems/apalache/blob/unstable/test/tla/y2k_instance.tla),
which instantiates `y2k.tla`:

```tla
{{#include ../../../test/tla/y2k_instance.tla::11}}
```

The downside of this approach is that you have to declare the variables of the
extended specification. This is easy with only two variables, but can quickly
become unwieldy.

## Convention over configuration

Alternatively, you can extend the base module and use overrides:

```tla
{{#include ../../../test/tla/y2k_override.tla::11}}
```

<a name="ConstInit"></a>
## ConstInit predicate

This approach is similar to the ``Init`` operator, but applied to the
constants. We define a special operator, e.g., called ``ConstInit``. For
instance, below is the example
[`y2k_cinit.tla`](https://github.com/informalsystems/apalache/blob/unstable/test/tla/y2k_cinit.tla):

```tla
{{#include ../../../test/tla/y2k_cinit.tla::13}}
```

To use `ConstInit`, pass it as the argument to `apalache`. For instance, for
`y2k_cinit`, we would run the model checker as follows:

```tla
$ cd $APALACHE_HOME/test/tla
$ apalache check --inv=Safety \
  --length=20 --cinit=ConstInit y2k_cinit.tla
```

### Parameterized initialization

As a bonus of this approach, Apalache allows one to check a specification over a
bounded set of parameters. For example:

```tla
CONSTANT N, Values

ConstInit ==
  /\ N \in 3..10
  /\ Values \in SUBSET 0..4
  /\ Values /= {}
```

The model checker will try the instances for all the combinations of
the parameters specified in ``ConstInit``, that is, in our example, it will
consider ``N \in 3..10`` and all non-empty value sets that are subsets of ``0..4``.

### Limitation

``ConstInit`` should be a conjunction of assignments and possibly of additional
constraints on the constants. For instance, you should not write `N = 10 \/ N =
20`. However, you can write `N \in {10, 20}`.

## TLC configuration file

We support configuring Apalache via TLC configuration files; these files are
produced automatically by TLA Toolbox, for example. TLC configuration files
allow one to specify which initialization predicate and transition predicate to
employ, which invariants to check, as well as to initialize specification
parameters. Some features of the TLC configuration files are not supported yet.
Check the manual page on ["Syntax of TLC Configuration Files"](./tlc-config.md).

_If you are checking a file `<myspec>.tla`, and the file `<myspec>.cfg` exists in
the same directory, it will be picked up by Apalache automatically. You can also
explicitly specify which configuration file to use via the `--config` option._
