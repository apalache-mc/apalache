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
 * Igor Konnov, Informal Systems, 2021-2022
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
 * NOTE: This operator is not supported by the model checker yet.
 * We are thinking about a reasonably simple implementation of it.
 *
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
VariantGetOnly(__tagName, __variant) ==
    \* default untyped implementation
    IF __variant.tag = __tagName
    THEN __variant.value
    ELSE \* trigger an error in TLC by choosing a non-existent element
         CHOOSE x \in { __variant }: x.tag = __tagName

(**
 * Return the value associated with the tag, when the tag equals to __tagName.
 * Otherwise, return __elseValue.
 *
 * @param `__tagName` the tag attached to the variant
 * @param `__variant` a variant that is constructed with `Variant(...)`
 * @param `__defaultValue` the default value to return, if not tagged with __tagName
 * @return the value extracted from the variant, or the __defaultValue
 *
 * Its type could look like follows:
 *
 *   (Str, Tag(a) | b, a) => a
 *)
VariantGetOrElse(__tagName, __variant, __defaultValue) ==
    \* default untyped implementation
    IF __variant.tag = __tagName
    THEN __variant.value
    ELSE __defaultValue


(**
 * Unsafely return a value of the type associated with __tagName.
 * If the variant is tagged with __tagName, then return the associated value.
 * Otherwise, return some value of the type associated with __tagName.
 *
 * @param `tagValue` the tag attached to the variant
 * @param `variant` a variant that is constructed with `Variant(...)`
 * @return the value extracted from the variant, when tagged __tagName;
 *         otherwise, return some value
 *
 * Its type could look like follows:
 *
 *   (Str, Tag(a) | b) => a
 *)
VariantGetUnsafe(__tagName, __variant) ==
    \* the default untyped implementation
    __variant.value
         
===============================================================================
