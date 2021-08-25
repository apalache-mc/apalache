-------------------------------- MODULE Bug914 --------------------------------

\* Minimal reproduction for https://github.com/informalsystems/apalache/issues/914
\*
\* The crash occurs when the the number of fields added to the record in `msgs'` in
\* the first disjunct of `Next` are greater than the number of fields declared for
\* the record in the type annotation of `msgs`.
\*
\* The selection of a set of empty records is just the minimal case in which this
\* numerical difference between the declared fields and the assigned fields can be
\* triggerd. I.e., this is not targeting a problem wherein the set of empty records
\* is an edge case.

VARIABLE
  \* @type: [];
  m

Init == m = [foo |-> TRUE]

Next ==
   \/ m' = [m EXCEPT !.foo = TRUE]
   \/ m' = [m EXCEPT !.foo = TRUE]

================================================================================
