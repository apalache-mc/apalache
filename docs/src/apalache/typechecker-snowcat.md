## The new type checker Snowcat

**WARNING:** Snowcat has not been integrated with the model checker yet. The
integration is coming soon. The model checker is still expecting the [old type
annotations](./types-and-annotations.md).

For the moment, you can use Snowcat as a standalone tool. New type annotations are written in comments, so they are
ignored by the model checker (until the integration happens). Hence, you can start writing new type annotations and
debug them with Snowcat. As the new type annotations are written in comments, they will be ignored by the model
checker (until the integration happens). Snowcat ignores the old annotations and warns the user about the new type
annotations. So you can start preparing for the transition to new annotations right now.

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

