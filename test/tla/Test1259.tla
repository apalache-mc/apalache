------------------ MODULE Test1259 ---------------------

VARIABLES
    \* @type: Str -> Int;
    fun

\* @type: (a -> b) => (a -> b);
Foo(f) ==
    LET f2 == f IN
    LET d == DOMAIN f2 IN
    [ x \in d |-> f[x] ]

Init ==
    fun = Foo([ x \in { "a" } |-> 1 ])

Next ==
    UNCHANGED fun

====================================================
