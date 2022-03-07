--------------------------- MODULE BinSearch7 ---------------------------------
(*
 * A tutorial version of binary search.
 *
 * Version 7. Introduce bounded integers.
 * Version 6. Check termination and progress.
 * Version 5. Check for all inputs (for a fixed bit width).
 * Version 4. Specify the loop (with a caveat).
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
    returnValue,
    \* The number of executed steps.
    \* @type: Int;
    nSteps

\* Addition over fix-width integers.
IAdd(i, j) ==
    \* add two integers with unbounded arithmetic
    LET res == i + j IN
    IF MIN_INT <= res /\ res <= MAX_INT
    THEN res
    ELSE \* wrap the result over 2^INT_WIDTH (probably redundant)
        LET wrapped == res % MAX_UINT IN
        IF wrapped <= MAX_INT
        THEN wrapped    \* a positive integer, return as is
        ELSE \* complement the value to represent it with an unbounded integer
          -(MAX_UINT - wrapped)

\* Initialization step (lines 2-3)
Init ==
    /\ low = 0
    /\ high = Len(INPUT_SEQ) - 1
    /\ isTerminated = FALSE
    /\ returnValue = 0
    /\ nSteps = 0

\* Computation step (lines 5-16)
Next ==
    IF ~isTerminated
    THEN IF low <= high
      THEN          \* lines 6-14
        /\ nSteps' = nSteps + 1
        /\ LET mid == IAdd(low, high) \div 2 IN
           LET midVal == INPUT_SEQ[mid + 1] IN
            \//\ midVal < INPUT_KEY \* lines 9-10
              /\ low' = IAdd(mid, 1)
              /\ UNCHANGED <<high, returnValue, isTerminated>>
            \//\ midVal > INPUT_KEY \* lines 11-12
              /\ high' = IAdd(mid, - 1)
              /\ UNCHANGED <<low, returnValue, isTerminated>>
            \//\ midVal = INPUT_KEY \* lines 13-14
              /\ returnValue' = mid
              /\ isTerminated' = TRUE
              /\ UNCHANGED <<low, high>>
      ELSE          \* line 16
        /\ isTerminated' = TRUE
        /\ returnValue' = -(low + 1)
        /\ UNCHANGED <<low, high, nSteps>>
    ELSE            \* isTerminated
      UNCHANGED <<low, high, returnValue, isTerminated, nSteps>>

InputIsSorted ==
    \* The most straightforward way to specify sortedness
    \* is to use two quantifiers,
    \* but that would produce O(Len(INPUT_SEQ)^2) constraints.
    \* Here, we write it a bit smarter.
    \A i \in DOMAIN INPUT_SEQ:
        i + 1 \in DOMAIN INPUT_SEQ =>
          INPUT_SEQ[i] <= INPUT_SEQ[i + 1]

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
    THEN \* Indices start with 1, whereas returnValue starts with 0
        returnValue + 1 \in MatchingIndices
    ELSE returnValue < 0

\* What we expect from the search when it is finished (it does not hold).
Postcondition ==
    isTerminated => ReturnValueIsCorrect

\* What we expect from the search when it is finished.
PostconditionSorted ==
    isTerminated => (~InputIsSorted \/ ReturnValueIsCorrect)

\* We know the exact number of steps to show termination.
Termination ==
    (nSteps >= INT_WIDTH) => isTerminated

\* By showing that the interval [low, high] is contracting,
\* we can implicitly show termination too.
Progress ==
    ~isTerminated' => (low' > low \/ high' < high)

===============================================================================

