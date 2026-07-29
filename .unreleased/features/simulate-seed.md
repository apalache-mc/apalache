Add `{check,simulate} --seed` and `search.seed` for reproducible SMT solving
and transition selection. When no SMT seed is set, the search seed is
propagated to the selected SMT backend, see #2083 and #3404.
