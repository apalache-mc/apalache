---- MODULE Updates ----
VARIABLE f
E4 == [ f EXCEPT ![0] = [@ EXCEPT !.state = 4] ]
================================
