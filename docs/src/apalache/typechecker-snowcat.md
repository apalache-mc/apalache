## The new type checker Snowcat

**WARNING:** Snowcat is our type checker starting with Apalache version 0.15.0.
If you are using Apalache prior to version 0.15.0, check the chapter on
[old type annotations](./types-and-annotations.md).

---------------------------------------------------------------------------------

### How to write type annotations

Check the [HOWTO](../HOWTOs/howto-write-type-annotations.md).  You can find
detailed syntax of type annotations in [ADR002](../adr/002adr-types.md). 

### How to run the type checker

The type checker can be run as follows:

```bash
$ apalache typecheck [--infer-poly=<bool>] <myspec>.tla
```

The arguments are as follows:

* General parameters:
    - `--infer-poly` controls whether the type checker should infer polymorphic
      types. As many specs do not need polymorphism, you can set this option
      to `false`. The default value is `true`.

There is not much to explain about running the tool. When it successfully finds
the types of all expressions, it reports:

```
 > Running Snowcat .::..
 > Your types are great!
  ...
Type checker [OK]
```

When the type checker finds an error, it explains the error like that:

```
 > Running Snowcat .::.
[QueensTyped.tla:42:44-42:61]: Mismatch in argument types. Expected: (Seq(Int)) => Bool
[QueensTyped.tla:42:14-42:63]: Error when computing the type of Solutions
 > Snowcat asks you to fix the types. Meow.
Type checker [FAILED]
```

