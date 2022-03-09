-------------------------- MODULE MC2_8 ---------------------------------------
\* an instance of BinSearch2 with all parameters fixed

\* fix 8 bits
INT_WIDTH == 8
\* the input sequence to try
\* @type: Seq(Int);
INPUT_SEQ == << >>
\* the element to search for
INPUT_KEY == 10

\* introduce the variables to be used in BinSearch2
VARIABLES
    \* @type: Int;
    low,
    \* @type: Int;
    high,
    \* @type: Bool;
    isTerminated,
    \* @type: Int;
    returnValue

\* use an instance for the fixed constants
INSTANCE BinSearch2
===============================================================================
