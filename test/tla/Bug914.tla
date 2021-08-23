-------------------------------- MODULE Bug914 --------------------------------

\* Minimal reproduction for https://github.com/informalsystems/apalache/issues/914

VARIABLE
  (* A set of empty records
    @type:  Set([]);
  *)
  msgs

Init == msgs = {}

Next ==
  \/ msgs' = {[ foo |-> FALSE ]}
  \/ \E m \in msgs: msgs' = {[ m EXCEPT !.foo = TRUE ]}

================================================================================
