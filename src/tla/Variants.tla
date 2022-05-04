------------------------------- MODULE Variants -------------------------------
(**
 * Operators on variants. Variants are a common programming pattern that allows
 * one to mix records of various shapes into a single set, sequence,
 * or a function.
 *
 * This module provides the default untyped implementation of the operators.
 * Apalache treats these operators as typed, so it enforces type safety of
 * variants.
 *
 * Igor Konnov, Informal Systems, 2021
 *)

(**
 * Wrap a record into a variant. The record must contain the field `tag`,
 * and the value of the tag field must be a string literal.
 *
 * @param rec a record that contains a field `tag`
 * @return the record wrapped in the variant type
 *
 * The type could look like follows, if we supported string literals in types:
 *
 *   { tag: Str, a } =>
 *     { tag: "$tagValue", a } | b
 *)
Variant(__rec) ==
    \* default untyped implementation
    __rec 

(**
 * Filter a set of variants with the provided tag value.
 *
 * @param `S` a set of variants that are constructed with `Variant(...)`
 * @param `tagValue` a string literal that is used to filter the set elements
 * @return the set of elements of S that are tagged with `tagValue`.
 *
 * The type could look like follows, if we supported string literals in types:
 *
 *   (Set({ tag: "$tagValue", a} | b), Str) => Set({ tag: Str, a })
 *)
FilterByTag(__S, __tagValue) ==
    \* default untyped implementation
    { __e \in S: __e.tag = __tagValue }


(**
 * Test the tag of `variant` against the value `tagValue`.
 * If `variant.tag = tagValue`, then apply `ThenOper(rec)`,
 * where `rec` is a record extracted from `variant`.
 * Otherwise, apply `ElseOper(reducedVariant)`,
 * where `reducedVariant` is a version of `variant` that does allow for
 * the tag `tagValue`.
 *
 * @param `variant` a variant that is constructed with `Variant(...)`
 * @param `tagValue` a string literal that is used to extract a record
 * @param `ThenOper` an operator that is called
 *        when `variant` is tagged with `tagValue`
 * @param `ElseOper` an operator that is called
 *        when `variant` is tagged with a value different from `tagValue`
 * @return the result returned by either `ThenOper`, or `ElseOper`
 *
 * The type could look like follows, if we supported string literals in types:
 *
 *   (
 *     { "$tagValue": { tag: Str, a } | b },
 *     { tag: Str, a } => r,
 *     Variant(b) => r
 *   ) => r
 *)
MatchTag(__variant, __tagValue, __ThenOper(_), __ElseOper(_)) ==
    \* default untyped implementation
    IF __variant.tag = __tagValue
    THEN __ThenOper(__variant)
    ELSE __ElseOper(__variant)

(**
 * In case when `variant` allows for one record type,
 * apply `ThenOper(rec)`, where `rec` is a record extracted from `variant`.
 * The type checker must enforce that `variant` allows for one record type.
 * The untyped implementation does not perform such a test,
 * as it is impossible to do so without types.
 *
 * @param `variant` a variant that is constructed with `Variant(...)`
 * @param `ThenOper` an operator that is called
 *        when `variant` is tagged with `tagValue`
 * @return the result returned by `ThenOper`
 *
 * The type could look like follows, if we supported string literals in types:
 *
 *   (
 *     { "$tagValue": { tag: Str, a } },
 *     { tag: Str, a } => r
 *   ) => r
 *)
 *)
MatchOnly(__variant, __ThenOper(_)) ==
    \* default untyped implementation
    __ThenOper(__variant)
===============================================================================
