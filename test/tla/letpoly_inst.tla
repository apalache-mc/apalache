------------------------- MODULE letpoly_inst ---------------------------------
\* A test that shows that parametric types can be instantiated.
\* A parametric operator should be replaced with its clone at the call site.
VARIABLE 
  \* @type: <<Int, Bool>>;
  pair

\* @type: (a -> b, a) => b;
A(f, e) ==
    f[e]

\* @type: (a -> a, a) => a;
B(f, e) ==
    \* we need different instances of A for different types of a
    A(f, e)

C ==
    LET f1 == [ x \in { 0, 1, 2 } |-> x ]
        f2 == [ x \in BOOLEAN |-> x ]
    IN
    LET r1 == B(f1, 1)      \* B is instantiated with a = Int
        r2 == B(f2, TRUE)   \* B is instantiated with a = Bool
    IN
    <<r1, r2>>

Init == 
  pair = <<0, FALSE>>

Next ==
  pair' = C
    
===============================================================================
