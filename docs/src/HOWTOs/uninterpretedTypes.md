# How to use uninterpreted types

This HOWTO explains what uninterpreted types are in the context of Apalache's type system,
outlined in [ADR002][], and where/how to use them.

## What are uninterpreted types?
It is often the case, when writing specifications, that inputs (`CONSTANTS`) describe a collection of values,
where the only relevant property is that all the values are considered unique.
For instance, [TwoPhase.tla][] defines 
```tla
CONSTANT RM \* The set of resource managers
```
however, for the purposes of specification analysis,
it does not matter if we instantiate `RM = 1..3` or `RM = {"a","b","c"}`,
because the only operators applied to elements of `RM` are polymorphic in the type of the elements of `RM`.

For this reason, Apalache supports a special kind of type annotation: uninterpreted types. 
The type checker [Snowcat][] makes sure that a value belonging to an uninterpreted type
is only ever passed to polymorphic operators, and, importantly, that it is never compared to a value of any other type. 

## When to use uninterpreted types?

For efficiency reasons, you should use uninterpreted types whenever a `CONSTANT` or value
represents (an element of) a collection of unique identifiers,
the precise value of which does not influence the properties of the specification.

On the other hand, if, for example, the order of values matters,
identifiers should likely be `1..N` and hold type `Int` instead of an uninterpreted type,
since `Int` values can be passed to the non-polymorphic `<,>,>=,<=` operators.

## How to annotate uninterpreted types
Following [ADR002][], an annotation with an uninterpreted type looks exactly like an annotation with a type alias:
```tla
\* @type: UTNAME;
```

where `UTNAME` matches the pattern `[A-Z_][A-Z0-9_]*`, and is not a type alias defined elsewhere.

## How to introduce values belonging to an uninterpreted type
Apalache uses the following convention-based naming scheme for values of uninterpreted types:
```tla
"identifier_OF_TYPENAME"
```
where:
  - `TYPENAME` is the uninterpreted type to which this value belongs, matching the pattern `[A-Z_][A-Z0-9_]*`, and
  - `identifier` is a unique identifier within the uninterpreted type, matching the pattern `[a-zA-Z0-9_]+`.

Example: `"1_OF_UT"` is a value belonging to the uninterpreted type `UT`, as is `"2_OF_UT"`.
These two values are distinct by definition.
On the contrary, `"1_OF_ut"` does _not_ meet the criteria for a value belonging to an uninterpreted type
(lowercase `ut` is not a valid identifier for an uninterpreted type), so it is treated as a string value.

**Note**: Values matching the pattern `"FRESH[0-9]+_OF_TYPENAME"` are reserved for internal use,
to allow Apalache to construct fresh values.

## Uninterpreted types, `Str`, and comparisons
Importantly, while both strings and values belonging to uninterpreted types are introduced using the `"..."` notation,
they are treated as having distinct, incomparable types.
Examples:
  - The following expression is type-incorrect:
    ```tla 
    "abc" = "bc_OF_A" \* Cannot compare values of types Str and A
    ```
  - The following expression is type-incorrect:
    ```tla 
    "1_OF_A" = "1_OF_B" \* Cannot compare values of types A and B
    ```
- The following expressions are type-correct:
    ```tla 
    \* Can compare 2 values of type A. 
    "1_OF_A" = "2_OF_A" \* = FALSE, identifiers are different
    "1_OF_A" = "1_OF_A" \* = TRUE, identifiers are the same
    ```



[ADR002]: ../adr/002adr-types.md
[Snowcat]: ../apalache/typechecker-snowcat.md 
[TwoPhase.tla]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla
