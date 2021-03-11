---------------------------- MODULE SafeMath -----------------------------------
(*
 * Test that the operations over big integers go through.
 * This specification is expected to deadlock, without violating the invariant.
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
POWER == 2^BITWIDTH
MAX_UNSIGNED == (2^BITWIDTH) - 1

VARIABLE
    \* @type: Str;
    opcode,
    \* @type: Int;
    arg1,
    \* @type: Int;
    arg2,
    \* @type: Int;
    res,
    \* @type: Bool;
    is_error

vars == <<opcode, arg1, arg2, res, is_error>>

InRange(i) ==
    i >= 0 /\ i <= MAX_UNSIGNED

TryAdd(a, b) ==
    LET c == (a + b) % POWER IN
    IF c < a
    THEN <<FALSE, 0>>
    ELSE <<TRUE, c>>

TrySub(a, b) ==
    IF b > a
    THEN <<FALSE, 0>>
    ELSE <<TRUE, (a - b) % POWER>>

TryMul(a, b) ==
    IF a = 0
    THEN <<TRUE, 0>>
    ELSE LET c == (a * b) % POWER IN
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
        /\ LET \* @type: <<Bool, Int>>;
               flag_and_c == Op(a, b) IN
            /\ opcode' = code
            /\ arg1' = a
            /\ arg2' = b
            /\ is_error' = ~flag_and_c[1]
            /\ res' = flag_and_c[2]

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
          \* The following operators are too hard for z3 to work out
          \* of the box. Perhaps, we have to use bitvectors.
          (*
          \/ TestTry("MUL", TryMul)
          \/ TestTry("DIV", TryDiv)
          \/ TestTry("MOD", TryMod)
            *)
    \/ opcode /= "NOP" /\ UNCHANGED vars

InvAdd ==
    LET perfectInt == arg1 + arg2 IN
    opcode = "ADD"
        => is_error <=> (perfectInt > MAX_UNSIGNED /\ res /= perfectInt)

InvSub ==
    LET perfectInt == arg1 - arg2 IN
    opcode = "SUB"
        => is_error <=> (perfectInt < 0 /\ res /= perfectInt)

InvMul ==
    LET perfectInt == arg1 * arg2 IN
    opcode = "MUL"
        => is_error <=> (perfectInt > MAX_UNSIGNED /\ res /= perfectInt)

InvDiv ==
    LET perfectInt == arg1 \div arg2 IN
    opcode = "DIV"
        => is_error <=>
            arg2 = 0 \/ (perfectInt > MAX_UNSIGNED /\ res /= perfectInt)

InvMod ==
    LET perfectInt == arg1 % arg2 IN
    opcode = "MOD"
        => is_error <=>
            arg2 = 0 \/ (perfectInt > MAX_UNSIGNED /\ res /= perfectInt)


\* check this to see an overflow
FalseInv ==
    arg1 + arg2 < MAX_UNSIGNED
==============================================================================
