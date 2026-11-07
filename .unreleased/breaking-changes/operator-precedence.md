Align PrettyWriter with the corrected tla2tools precedence: `SUBSET` and `UNION`
have precedence 8, and `DOMAIN` has precedence 9. Existing specifications that
rely on the old binding need explicit parentheses, for example `(SUBSET S) \cup T`
and `(DOMAIN f) .. n`. `SUBSET 1 .. 3` now means `SUBSET (1 .. 3)`.
See [tlaplus/tlaplus#1508](https://github.com/tlaplus/tlaplus/pull/1508).
