---------------------------- MODULE TestVariants -------------------------------
(*
 * Functional tests for operators over variants.
 * We introduce a trivial state machine and write tests as state invariants.
 *)

EXTENDS Integers, FiniteSets, Apalache, Variants

Init == TRUE
Next == TRUE

(* DEFINITIONS *)

\* A variant that belongs to a more general type.
\*
\* @type: A(Int) | B({ value: Str });
VarA == Variant("A", 1)

\* A variant that belongs to a more general type.
\*
\* @type: A(Int) | B({ value: Str });
VarB == Variant("B", [ value |-> "hello" ])

\* A singleton variant, e.g., to be used with a filter.
\*
\* @type: C({ value: Str });
VarC == Variant("C", [ value |-> "world" ])

TestVariant ==
    VarA \in { VarA, VarB }

TestVariantFilter ==
    \E v \in VariantFilter("B", { VarA, VarB }):
        v.value = "hello"

TestVariantTag ==
    VariantTag(VarC) = "C"

TestVariantGetUnsafe ==
    \* The unsafe version gives us only a type guarantee.
    VariantGetUnsafe("A", VarB) \in Int

TestVariantGetOrElse ==
    \* When the tag name is different from the actual one, return the default value.
    VariantGetOrElse("A", VarB, 12) = 12

AllTests ==
    /\ TestVariant
    /\ TestVariantFilter
    /\ TestVariantTag
    /\ TestVariantGetUnsafe
    /\ TestVariantGetOrElse

===============================================================================
