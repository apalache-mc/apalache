--------------------------- MODULE BinSearch3 ---------------------------------
(*
 * A tutorial version of binary search.
 *
 * Version 3. Specify the expected postcondition.
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
      THEN        \* lines 6-14: not implemented yet
        UNCHANGED <<low, high, isTerminated, returnValue>>
      ELSE          \* line 16
        /\ isTerminated' = TRUE
        /\ returnValue' = -(low + 1)
        /\ UNCHANGED <<low, high>>
    ELSE            \* isTerminated
      UNCHANGED <<low, high, returnValue, isTerminated>>

\* We can get an idea about the expected result of the search from the source:
\*
\* https://github.com/openjdk/jdk/blob/d7f31d0d53bfec627edc83ceb75fc6202891e186/src/java.base/share/classes/java/util/Arrays.java#L1662-L1698
\*
\* The property of particular interest is this one:
\*
\* "Note that this guarantees that the return value will be >= 0 if
\*  and only if the key is found."
ReturnValueIsCorrect ==
    LET MatchingIndices ==
        { i \in DOMAIN INPUT_SEQ: INPUT_SEQ[i] = INPUT_KEY }
    IN
    IF MatchingIndices /= {}
    THEN \* Indices in TLA+ start with 1, whereas the Java returnValue starts with 0
        returnValue + 1 \in MatchingIndices
    ELSE returnValue < 0

\* What we expect from the search when it is finished.
Postcondition ==
    isTerminated => ReturnValueIsCorrect

===============================================================================

