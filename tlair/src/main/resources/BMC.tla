-------------------------------- MODULE bmc --------------------------------
\* Utility functions that can be used to help BMCMT, e.g., type annotations

(*
 This action annotates the argument expression with the type passed as a string.
 This type annotation is parsed by BMCMT and should follow the syntax of type terms,
 which are inductively defined as follows:
 
 - ConstT
 - BoolT
 - IntT
 - FinSetT(elementType)
 - PowSetT(baseSetType)
 - FunT(domainType, resultType)
 - FinFunSetT(domainType, codomainType)
 - TupleT(type_1, ..., type_n)
 - RecordT(name_1, type_1, ..., name_n, type_n)
 *)
WithType(expr, type_string) == expr 

=============================================================================
\* Modification History
\* Last modified Thu Jul 12 17:26:05 CEST 2018 by igor
\* Created Thu Jul 12 17:17:22 CEST 2018 by igor
