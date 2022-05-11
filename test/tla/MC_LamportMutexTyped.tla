-------------------- MODULE MC_LamportMutexTyped ------------------------------
\* an instance to run the model checker

\* a fixed number of processes
N == 3

\* an upper bound on the clock value
maxClock == 10

VARIABLES
  \* @type: Int -> Int;
  clock,    \* local clock of each process
  \* @type: Int -> (Int -> Int);
  req,      \* requests received from processes (clock transmitted with request)
  \* @type: Int -> Set(Int);
  ack,      \* acknowledgements received from processes
  \* @typeAlias: MESSAGE = {
  \*     type: Str,
  \*     clock: Int
  \* };
  \* @type: Int -> (Int -> Seq(MESSAGE));
  network,  \* messages sent but not yet received
  \* @type: Set(Int);
  crit      \* set of processes in critical section

INSTANCE LamportMutexTyped
===============================================================================
