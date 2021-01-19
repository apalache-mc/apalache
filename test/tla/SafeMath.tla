---------------------------- MODULE SafeMath -----------------------------------
(*
 * Test that the operations over big integers go through.
 * This specification is expected to deadlock, but not violating the invariant.
 *
 * Here we are testing SafeMath:
 *
 * https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/math/SafeMath.sol
 *
 * More on the topic:
 *
\* https://medium.com/coinmonks/math-in-solidity-part-2-overflow-3cd7283714b4
\* https://medium.com/@soliditydeveloper.com/solidity-design-patterns-multiply-before-dividing-407980646f7
 *
 * Igor Konnov, 2021
 *)
EXTENDS Integers

\* the width of the unsigned integers, like in Solidity
BITWIDTH == 256
MAX_UNSIGNED == (2^BITWIDTH) - 1

VARIABLE opcode, arg1, arg2, res, is_error

vars == <<opcode, arg1, arg2, res, is_error>>

InRange(i) ==
    i >= 0 /\ i <= MAX_UNSIGNED

TryAdd(a, b) ==
    LET c == (a + b) % MAX_UNSIGNED IN
    IF c < a
    THEN <<FALSE, 0>>
    ELSE <<TRUE, c>>

TrySub(a, b) ==
    IF b > a
    THEN <<FALSE, 0>>
    ELSE <<TRUE, (a - b) % MAX_UNSIGNED>>

TryMul(a, b) ==
    IF a = 0
    THEN <<TRUE, 0>>
    ELSE LET c == (a * b) % MAX_UNSIGNED IN
        IF c \div a /= b
        THEN <<FALSE, 0>>
        ELSE <<TRUE, c>>

TryDiv(a, b) ==
    IF b = 0
    THEN <<FALSE, 0>>
    ELSE <<TRUE, a \div b>>

TryMod(a, b) ==
    IF b = 0
    THEN <<FALSE, 0>>
    ELSE <<TRUE, a % b>>

TestTry(code, Op(_, _)) ==
    \* non-deterministically pick two non-negative integers
    \E a, b \in Int:
        /\ InRange(a)
        /\ InRange(b)
        /\ LET flag_c == Op(a, b) IN
            /\ opcode' = code
            /\ arg1' = a
            /\ arg2' = b
            /\ is_error' = flag_c[1]
            /\ res' = flag_c[2]

Init ==
    /\ opcode = "NOP"
    /\ arg1 = 0
    /\ arg2 = 0
    /\ res = 0
    /\ is_error = FALSE

Next ==
    \/ /\ opcode = "NOP"
       /\ \/ TestTry("ADD", TryAdd)
          \/ TestTry("SUB", TrySub)
          \/ TestTry("MUL", TryMul)
          \/ TestTry("DIV", TryDiv)
          \/ TestTry("MOD", TryMod)
    \/ opcode /= "NOP" /\ UNCHANGED vars

Inv ==
    /\ opcode = "ADD"
        => is_error <=> (arg1 + arg2 > MAX_UNSIGNED \/ res /= arg1 + arg2)
    /\ opcode = "SUB"
        => is_error <=> (arg1 - arg2 < 0 \/ res /= arg1 - arg2)
    /\ opcode = "MUL"
        => is_error <=> (arg1 * arg2 > MAX_UNSIGNED \/ res /= arg1 * arg2 )
    /\ opcode = "DIV"
        => is_error <=>
            arg2 = 0 \/ arg1 \div arg2 > MAX_UNSIGNED \/ res /= arg1 \div arg2
    /\ opcode = "MOD"
        => is_error <=>
            arg2 = 0 \/ arg1 % arg2 > MAX_UNSIGNED \/ res /= arg1 % arg2


\* check this to see an overflow
FalseInv ==
    arg1 + arg2 < MAX_UNSIGNED
==============================================================================
