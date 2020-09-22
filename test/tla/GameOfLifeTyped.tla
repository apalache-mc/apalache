---------------------------- MODULE GameOfLifeTyped --------------------------
\* THIS IS A TYPED VERSION OF GameOfLife
\* The original is avaiable at: 
\* https://github.com/tlaplus/Examples/tree/master/specifications/GameOfLife
\*
EXTENDS Integers, Typing

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

TypeAssumptions ==
  /\ AssumeType(N, "Int")
  /\ AssumeType(grid, "<<Int, Int>> -> Bool")

vars == grid

RECURSIVE Sum(_, _)
Sum(f, S) == "(<<Int, Int>> -> Int, Set(<<Int, Int>>)) => Int" :>
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  f[x] + Sum(f, S \ {x})

\* The type check fails on <<1, 2>>. We need an explicit annotation.
Tup2(x, y) ==
    LET tup == "<<Int, Int>>" :> <<x, y>> IN tup

Pos ==
    {Tup2(x, y): x, y \in 1..N}

TypeOK == grid \in [Pos -> BOOLEAN]

sc[<<x, y>> \in (0 .. N + 1) \X
                (0 .. N + 1)] == CASE \/ x = 0 \/ y = 0
                                      \/ x > N \/ y > N
                                      \/ ~grid[Tup2(x, y)] -> 0
                                   [] OTHER -> 1

score(p) == "<<Int, Int>> => Int" :>
            LET nbrs == {x \in {-1, 0, 1} \X
                               {-1, 0, 1} : x /= Tup2(0, 0)}
                points == {Tup2(p[1] + x, p[2] + y) : <<x, y>> \in nbrs}
            IN Sum(sc, points)
                   
Init == grid \in [Pos -> BOOLEAN]
Next == grid' = [p \in Pos |-> IF \/  (grid[p] /\ score(p) \in {2, 3})
                                  \/ (~grid[p] /\ score(p) = 3)
                                THEN TRUE
                                ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================
