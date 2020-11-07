------------------------------ MODULE Config -------------------------------------------
(* a specification to check whether the configuration files are parsed *)
EXTENDS Integers

VARIABLES x

\* the default init
Init ==
    x = 0

\* the init predicate we set in .cfg
Init1 ==
    x = 1

\* the init predicate that we override with command-line options
Init2 ==
    x = 2

\* the default transition predicate
Next ==
    UNCHANGED x

\* the transition predicate we set in .cfg
Next1 ==
    x' = x + 1

\* the next predicate that we override with command-line options
Next2 ==
    x' = x + 2

Spec ==
    Init /\ [][Next]_x

Spec2 ==
    Init2 /\ [][Next2]_x

\* the default invariant
Inv ==
    x < 1

\* the invariant we set in .cfg
Inv1 ==
    x < 15

\* the invariant that we override with command-line options
Inv2 ==
    x < 25

AwesomeLiveness ==
    <>(x > 10)

========================================================================================
