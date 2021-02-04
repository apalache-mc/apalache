---------------------- MODULE FiniteSetsExtTyped ---------------------------
(* This is a test version of FiniteSetsExt that can be obtained from:

   https://github.com/tlaplus/CommunityModules/blob/master/modules/FiniteSetsExt.tla

  We annotate the original module with types.

  The orignal license:

*****************************************************************************
MIT License

Copyright (c) 2019 TLA+

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*****************************************************************************
 *)

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

\* not using LOCAL until issue #543 is fixed
(*LOCAL*) INSTANCE FunctionsTyped



ReduceSet(op(_, _), set, acc) ==
  (***************************************************************************)
  (* TLA+ forbids recursive higher-order operators, but it is fine with      *)
  (* recursive functions.  ReduceSet generates a recursive function over the *)
  (* subsets of a set, which can be used to recursively run a defined        *)
  (* operator.  This can then be used to define other recursive operators.   *)
  (* The op is assumed to be an abelian/commutative operation.               *)
  (***************************************************************************)
  LET f[s \in SUBSET set] ==
    IF s = {} THEN acc
    ELSE LET x == CHOOSE x \in s: TRUE
         IN op(x, f[s \ {x}])
  IN f[set]


Sum(set) == ReduceSet(LAMBDA x, y: x + y, set, 0)

Product(set) == ReduceSet(LAMBDA x, y: x * y, set, 1)

-----------------------------------------------------------------------------

Quantify(S, P(_)) ==
   (*************************************************************************)
   (* Quantify the elements in S matching the predicate (LAMDBA) P.         *)
   (*                                                                       *)
   (* This operator is overridden by FiniteSetsExt#quantify whose           *)
   (* implementation does *not* enumerate the intermediate set! This is     *)
   (* the only advantage that Quantify(...) has over Cardinality(...).      *)
   (*                                                                       *)
   (* Example:                                                              *)
   (*          Quantify(1..9, LAMBDA n : n % 2 = 0) = 4                     *)
   (*************************************************************************)
   Cardinality({s \in S : P(s)})

-----------------------------------------------------------------------------

kSubset(k, S) == 
   (*************************************************************************)
   (* A k-subset ks of a set S has Cardinality(ks) = k.  The number of      *)
   (* k-subsets of a set S with Cardinality(S) = n is given by the binomial *)
   (* coefficients n over k.  A set S with Cardinality(S) = n has 2^n       *)
   (* k-subsets.  \A k \notin 0..Cardinality(S): kSubset(k, S) = {}.        *)
   (*                                                                       *)
   (* This operator is overridden by FiniteSetsExt#kSubset whose            *)
   (* implementation, contrary to  { s \in SUBSET S : Cardinality(s) = k }, *)
   (* only enumerates the k-subsets of S and not all subsets.               *)
   (*                                                                       *)
   (* Example:                                                              *)
   (*          kSubset(2, 1..3) = {{1,2},{2,3},{3,1}}                       *)
   (*************************************************************************)
   { s \in SUBSET S : Cardinality(s) = k }

-----------------------------------------------------------------------------

(***************************************************************************)
(* We define Max(S) and Min(S) to be the maximum and minimum,              *)
(* respectively, of a finite, non-empty set S of integers.                 *)
(***************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

-----------------------------------------------------------------------------

(***************************************************************************) 
(* Compute all sets that contain one element from each of the input sets:  *)
(*                                                                         *)
(* Example:                                                                *)
(*          Choices({{1,2}, {2,3}, {5}}) =                                 *)
(*                         {{2, 5}, {1, 2, 5}, {1, 3, 5}, {2, 3, 5}}       *)
(***************************************************************************) 
Choices(Sets) == LET ChoiceFunction(Ts) == { f \in [Ts -> UNION Ts] : 
                                               \A T \in Ts : f[T] \in T }
                 IN  { Range(f) : f \in ChoiceFunction(Sets) }

-----------------------------------------------------------------------------

(***************************************************************************)
(* Chooses unique element from the input set matching the predicate        *)
(* (LAMDBA) P.                                                             *)
(*                                                                         *)
(* Contrary to CHOOSE, fails with                                          *)
(*      "CHOOSE x \\in S: P, but no element of S satisfied P:              *)
(* not just if P(_) holds for none of the elements in S, but also if       *)
(* P(_) holds for more than one element in S.                              *)
(*                                                                         *)
(* Example:                                                                *)
(*          ChooseUnique({2, 3, 4, 5}, LAMBDA x : x % 3 = 1) = 4           *)
(*                                                                         *)
(***************************************************************************)
ChooseUnique(S, P(_)) == CHOOSE x \in S :
                              P(x) /\ \A y \in S : P(y) => y = x

=============================================================================
