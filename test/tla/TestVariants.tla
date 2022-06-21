---------------------------- MODULE TestVariants -------------------------------
(*
 * Functional tests for operators over variants.
 * We introduce a trivial state machine and write tests as state invariants.
 *)

EXTENDS Integers, FiniteSets, Apalache, Variants

Init == TRUE
Next == TRUE

(* DEFINITIONS *)

VarA == Variant("A", 1)

VarB == Variant("B", [ value |-> "hello" ])

TestVariant ==
    VarA \in { VarA, VarB }

TestVariantFilter ==
    \E v \in VariantFilter("B", { VarA, VarB }):
        v.value = "hello"

TestVariantGetOnly ==
    \* We could just pass "hello", without wrapping it in a record.
    \* But we want to see how it works with records too.
    VariantGetOnly("B", VarB) = [ value |-> "hello" ]

TestVariantGetUnsafe ==
    \* The unsafe version gives us only a type guarantee.
    VariantGetUnsafe("A", VarB) \in Int

TestVariantGetOrElse ==
    \* When the tag name is different from the actual one, return the default value.
    VariantGetOrElse("A", VarB, 12) = 12

TestVariantMatch ==
    VariantMatch(
        "A",
        VarA,
        LAMBDA i: i > 0,
        LAMBDA v: FALSE
    )

AllTests ==
    /\ TestVariant
    /\ TestVariantFilter
    /\ TestVariantGetOnly
    /\ TestVariantGetUnsafe
    /\ TestVariantGetOrElse
    \* Disabled as unsupported by the model checker yet
    \*/\ TestVariantMatch

===============================================================================
