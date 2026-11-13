Fix missed violations: the membership of a skolemized `\E f \in [S -> T]` (and `x' \in [S -> T]`)
was asserted globally, so a co-domain `T` that is empty in some state ruled out every execution
through that state (sibling of #3503)
