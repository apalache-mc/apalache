Add `{check,simulate} --seed` and the typed `checker.seed` configuration field
for reproducible SMT solving and transition selection. When omitted, Apalache
generates and logs a fresh seed. The resolved seed is propagated to the
selected SMT backend, see #2083 and #3404.
