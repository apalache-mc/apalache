--------------- MODULE testReviewerCorrect -------------
EXTENDS Naturals
VARIABLE x

Init == TRUE

Inv  == TRUE

A == LET F(p) == p
     IN
        LET G == <<F(1), F(TRUE)>>
        IN G[1]


Next == x' = x
============================================