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
 * Wrap a value with a variant.
 *
 * @param rec a value
 * @return the record wrapped in the variant type
 *
 * The type looks like follows, when __tagName == "Tag":
 *
 *   (Str, a) => Tag(a) | b
 *)
Variant(__tagName, __value) ==
    \* default untyped implementation
    [ tag |-> __tagName, value |-> __value ]

(**
 * Filter a set of variants with the provided tag value.
 *
 * @param `S` a set of variants that are constructed with `Variant(...)`
 * @param `tagValue` a constant string that is used to filter the set elements
 * @return the set of elements of S that are tagged with `tagValue`.
 *
 * The type looks like follows, when __tagName == "Tag":
 *
 *   (Str, Set(Tag(a) | b)) => Set(a)
 *)
VariantFilter(__tagName, __S) ==
    \* default untyped implementation
    { __d \in { __e \in __S: __e.tag = __tagName }: __d.value }


(**
 * Test the tag of `variant` against the value `tagValue`.
 * If `variant.tag = tagValue`, then apply `ThenOper(rec)`,
 * where `rec` is a record extracted from `variant`.
 * Otherwise, apply `ElseOper(reducedVariant)`,
 * where `reducedVariant` is a version of `variant` that does allow for
 * the tag `tagValue`.
 *
 * @param `variant` a variant that is constructed with `Variant(...)`
 * @param `tagValue` a constant string that is used to extract a record
 * @param `ThenOper` an operator that is called
 *        when `variant` is tagged with `tagValue`
 * @param `ElseOper` an operator that is called
 *        when `variant` is tagged with a value different from `tagValue`
 * @return the result returned by either `ThenOper`, or `ElseOper`
 *
 * The type could look like follows, when __tagName == "Tag":
 *
 *   (
 *     Str,
 *     Tag(a) | b,
 *     a => r,
 *     Variant(b) => r
 *   ) => r
 *)
VariantMatch(__tagName, __variant, __ThenOper(_), __ElseOper(_)) ==
    \* default untyped implementation
    IF __variant.tag = __tagName
    THEN __ThenOper(__variant.value)
    ELSE __ElseOper(__variant)

(**
 * In cases where `variant` allows for one value,
 * extract the associated value and return it.
 * The type checker must enforce that `variant` allows for one option.
 *
 * @param `tagValue` the tag attached to the variant
 * @param `variant` a variant that is constructed with `Variant(...)`
 * @return the value extracted from the variant
 *
 * Its type could look like follows:
 *
 *   (Str, Tag(a)) => a
 *)
VariantGet(__tagName, __variant) ==
    \* default untyped implementation
    IF __variant.tag = __tagName
    THEN __variant.value
    ELSE \* trigger an error in TLC by choosing a non-existant element
         CHOOSE x \in { __variant }: x.tag = __tagName
===============================================================================
