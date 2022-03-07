--------------------------- MODULE BinSearch2 ---------------------------------
(*
 * A tutorial version of binary search.
 *
 * Version 2. The base case, no loop.
 * Version 1. Initial spec.
 * Version 0. The standard template.
 *)
EXTENDS Integers, Sequences, Apalache

CONSTANTS
    \* The input sequence.
    \*
    \* @type: Seq(Int);
    INPUT_SEQ,
    \* The key to search for.
    \*
    \* @type: Int;
    INPUT_KEY,
    \* Bit-width of machine integers.
    \*
    \* @type: Int;
    INT_WIDTH

\* the largest value of an unsigned integer
MAX_UINT == 2^INT_WIDTH
\* the largest value of a signed integer
MAX_INT  == 2^(INT_WIDTH - 1) - 1
\* the smallest value of a signed integer
MIN_INT  == -2^(INT_WIDTH - 1)

VARIABLES
    \* The low end of the search interval (inclusive).
    \* @type: Int;
    low,
    \* The high end of the search interval (inclusive).
    \* @type: Int;
    high,
    \* Did the algorithm terminate.
    \* @type: Bool;
    isTerminated,
    \* The result when terminated.
    \* @type: Int;
    returnValue

\* Initialization step (lines 2-3)
Init ==
    /\ low = 0
    /\ high = Len(INPUT_SEQ) - 1
    /\ isTerminated = FALSE
    /\ returnValue = 0

\* Computation step (lines 5-16)
Next ==
    IF ~isTerminated
    THEN IF low <= high
      THEN          \* lines 6-14: not implemented yet
        UNCHANGED <<low, high, isTerminated, returnValue>>
      ELSE          \* line 16
        /\ isTerminated' = TRUE
        /\ returnValue' = -(low + 1)
        /\ UNCHANGED <<low, high>>
    ELSE            \* isTerminated
      UNCHANGED <<low, high, returnValue, isTerminated>>

===============================================================================

