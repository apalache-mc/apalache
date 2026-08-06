Set filter `{ x \in SUBSET T : p }` is now supported. Apalache expands `SUBSET T`
into all 2^n subsets before applying the filter predicate, subject to the existing
`POWSET_MAX_BASE_SIZE = 20` limit.
