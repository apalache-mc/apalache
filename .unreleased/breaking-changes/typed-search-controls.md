Remove the tuning keys `search.seed`, `smt.randomSeed`, `z3.sat.random_seed`,
`z3.nlsat.seed`, and `z3.smt.random_seed`. Use the checker configuration field
`checker.seed`. Also replace `search.simulation`, `search.simulation.maxRun`,
and `search.outputTraces` with `search-kind`, `max-run`, and `output-traces`,
respectively, see #3404.
