--------------------------- MODULE MC_BasicChecker ----------------------------
EXTENDS Integers, Solver_typedefs

STATES == 0..6

INIT_STATES == { 0, 2 }

\* @type: Set(<<Int, Int>>);
TRANSITIONS == {
  <<0, 2>>,
  <<1, 2>>,
  <<2, 3>>,
  <<3, 1>>,
  <<3, 4>>,
  <<4, 3>>
}

INVARIANT == 0..3

MAX_STEPS == 10

VARIABLES
    \* @type: { code: Str, trace: Seq(Int) };
    searchState,
    \* @type: Int;
    stepNo,
    \* @type: CONTEXT;
    context

INSTANCE BasicChecker
===============================================================================
