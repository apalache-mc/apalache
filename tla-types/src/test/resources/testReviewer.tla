--------------- MODULE testReviewer -------------
EXTENDS Naturals
VARIABLE x

Init == TRUE

Inv  == TRUE

A == LET F(p) == p
     IN
        LET G(H(_)) == <<H(1), H(TRUE)>>
        IN G(F)[1]

Next == x' = x
============================================