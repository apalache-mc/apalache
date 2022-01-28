------------------ MODULE Test1259 ---------------------

VARIABLES
    \* @type: Bool;
    fun

\* @type: (a -> b) => Bool;
Foo(f) ==
    LET f2 == f IN
    LET d == DOMAIN f2 IN
    d = DOMAIN f

Init ==
    fun = Foo([ x \in { "a" } |-> 1 ])

Next ==
    UNCHANGED fun

====================================================
