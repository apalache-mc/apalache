# The Apalache Module

Similar to the `TLC` module, we provide the module called `Apalache`, which can
be found in
[src/tla](https://github.com/informalsystems/apalache/tree/unstable/src/tla).
Most of the operators in that modules are introduced internally by Apalache,
when it is rewriting a TLA+ specification.  It is useful to read the comments
to the operators defined in `Apalache.tla`, as they will help you in
understanding the [detailed output](./running.md#detailed) produced by the tool, see.
Perhaps, the most interesting operator in `Apalache` is the type assignment
operator that is defined as follows:

```tla
x := e == x = e
```

See the [discussion](./principles.md#assignments) on the role of assignments in Apalache.
