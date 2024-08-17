## 0.45.0 - 2024-08-17

### Features

- Handle expressions such as  S \in SUBSET [ a : Int ]  by rewriting the expression into  \A r \in S: DOMAIN r = {"a"} /\ r.a \in Int
- Translate Quint's generate into `Apalache!Gen` (#2916)
- Add `--timeout-smt` to limit SMT queries (#2936)
