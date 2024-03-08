When converting Quint lambdas, derive the return type from the Quint type inferred for 
the lambda, rather the type inferred for the body expression, avoiding mismatches with
Apalache type variables. (#2856)
