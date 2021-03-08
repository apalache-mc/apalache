------------------------ MODULE PascalTriangle --------------------------------
(*
 Pascal triangle:
 https://en.wikipedia.org/wiki/Pascal%27s_triangle#:~:text=In%20mathematics%2C%20Pascal's%20triangle%20is,theory%2C%20combinatorics%2C%20and%20algebra.

 This is a test for recursive functions of multiple arguments in TLA+.

 Igor Konnov, 2021
 *)

EXTENDS Integers

N == 5

Range == 0..N

\* Pascal's triangle defined as a recursive function
tri[n \in Range, k \in Range] ==
    IF k > n \/ (k = 0 /\ n = 0)
    THEN 1
    ELSE tri[n - 1, k - 1] + tri[n - 1, k]


VARIABLE
    \* @type: Int;
    result

Init ==
    result = tri[4, 2]

Next ==
    UNCHANGED result

Inv ==
    result = 6
    

===============================================================================
