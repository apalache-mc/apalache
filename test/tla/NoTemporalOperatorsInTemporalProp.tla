---- MODULE NoTemporalOperatorsInTemporalProp ----

\* Tests behaviour when boolean and temporal operators are mixed

EXTENDS Integers

VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y

Init ==
    /\ x = 0
    /\ y = 1

Next ==
    /\ x' = y
    /\ y' = x

\* the following two should give the same result
Property == x = 0
PropertyWithTemporal == x = 0 /\ []TRUE
ExplicitInvariant == [] (x = 0)

====