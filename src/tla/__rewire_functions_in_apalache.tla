--------------------------- MODULE Functions ---------------------------------
\*------ MODULE __rewire_functions_in_apalache -----------------------
(**
 * ^^^^^^^^^^^^^^^^^^^^^^ We have to call this module Functions in any
 * case, otherwise, SANY complains.
 *
 * This file contains alternative definitions for the operators defined in
 * Functions. Most importantly, we are adding type annotations. We also
 * define the Apalache-compatible behavior.
 *
 * These definitions are automatically rewired by the Apalache importer.
 *
 * Compare with the original definitions in Functions.tla:
 *
 * https://github.com/tlaplus/CommunityModules/blob/master/modules/Functions.tla
 *)

LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE __apalache_folds 

(**
 * Restriction of a function to a set (should be a subset of the domain).
 *
 * @type: (a -> b, Set(a)) => (a -> b);
 *)
Restrict(f, S) == [ x \in S |-> f[x] ]

(**
 * Range of a function.
 * Note: The image of a set under function f can be defined as
 *       Range(Restrict(f,S)).
 *
 * @type: (a -> b) => Set(b);
 *)
Range(f) == { f[x] : x \in DOMAIN f }

(**
 * The inverse of a function.
 * Example:
 *    LET f == ("a" :> 0 @@ "b" :> 1 @@ "c" :> 2)
 *    IN Inverse(f, DOMAIN f, Range(f)) =
 *                                 (0 :> "a" @@ 1 :> "b" @@ 2 :> "c")
 * Example:
 *    LET f == ("a" :> 0 @@ "b" :> 1 @@ "c" :> 2)
 *    IN Inverse(f, DOMAIN f, {1,3}) =
 *                                 1 :> "b" @@ 3 :> "a")
 *
 * @type: (a -> b, Set(a), Set(b)) => (b -> a);
 *)
Inverse(f, S, T) == [t \in T |-> CHOOSE s \in S: t \in Range(f) => f[s] = t]

(**
 * The inverse of a function.
 *
 * @type: (a -> b) => (b -> a);
 *)
AntiFunction(f) == Inverse(f, DOMAIN f, Range(f))

(**
 * A function is injective iff it maps each element in its domain to a
 * distinct element.
 *
 * This definition is overridden by TLC in the Java class SequencesExt.
 * The operator is overridden by the Java method with the same name.
 *
 * @type: (a -> b) => Bool;
 *)
IsInjective(f) ==
    \A a, b \in DOMAIN f:
        f[a] = f[b] => a = b

(**
 * Set of injections between two sets.
 *
 * @type: (Set(a), Set(b)) => Set(a -> b);
 *)
Injection(S, T) == { f \in [S -> T]: IsInjective(f) }

(**
 * This operator is not defined in the community modules.
 * As a temporary workaround, we define it globally.
 * It should be declared as LOCAL, once this issue is fixed:
 * https://github.com/informalsystems/apalache/issues/1495
 *
 * @type: (Set(a), Set(b), a -> b) => Bool;
 *)
IsSurjective(S, T, f) ==
    \A t \in T:
        \E s \in S:
            f[s] = t

(**
 * A map is a surjection iff for each element in the range there is some
 * element in the domain that maps to it.
 *
 * @type: (Set(a), Set(b)) => Set(a -> b);
 *)
Surjection(S, T) ==
    { f \in [S -> T]: IsSurjective(S, T, f) }

(**
 * A map is a bijection iff it is both an injection and a surjection.
 *
 * @type: (Set(a), Set(b)) => Set(a -> b);
 *)
Bijection(S, T) ==
    { f \in [S -> T]: IsSurjective(S, T, f) /\ IsInjective(f) }

(**
 * An injection, surjection, or bijection exists if the corresponding set
 * is nonempty.
 *)

(**
 * Is there an injection between S and T. Apalache defines it only on finite sets.
 *
 * @type: (Set(a), Set(b)) => Bool;
 *)
ExistsInjection(S, T)  ==
    Cardinality(S) <= Cardinality(T)

(**
 * Is there a surjection between S and T. Apalache defines it only on finite sets.
 *
 * @type: (Set(a), Set(b)) => Bool;
 *)
ExistsSurjection(S, T) ==
    Cardinality(S) >= Cardinality(T)

(**
 * Is there a bijection between S and T. Apalache defines it only on finite sets.
 *
 * @type: (Set(a), Set(b)) => Bool;
 *)
ExistsBijection(S, T)  ==
    Cardinality(S) = Cardinality(T)


(**
 * Applies the binary function op on all elements of seq in arbitrary
 * order starting with op(f[k], base). The resulting function is:
 *    op(f[i],op(f[j], ..., op(f[k],base) ...))
 *
 * op must be associative and commutative, because we can not assume a
 * particular ordering of i, j, and k
 *
 * Example:
 *  FoldFunction(LAMBDA x,y: {x} \cup y, {}, <<1,2,1>>) = {1,2}
 *
 * @type: ((b, c) => c, c, a -> b) => c;
 *)
FoldFunction(op(_, _), base, fun) ==
  \* note that ApalacheFoldSet is accumulating the result in the left argument,
  \* whereas FoldFunction is accumulating the result in the right argument.
  LET Map(y, x) == op(fun[x], y) IN
  __ApalacheFoldSet(Map, base, DOMAIN fun)


(**
 * Applies the binary function op on the given indices of seq in arbitrary
 * order starting with op(f[k], base). The resulting function is:
 *    op(f[i],op(f[j], ..., op(f[k],base) ...))
 *
 * op must be associative and commutative, because we can not assume a
 * particular ordering of i, j, and k
 *
 * indices must be a subset of DOMAIN(fun)
 *
 * Example:
 *  FoldFunctionOnSet(LAMBDA x,y: {x} \cup y, {}, <<1,2>>, {}) = {}
 *
 * @type: ((b, c) => c, c, a -> b, Set(a)) => c;
 *)
FoldFunctionOnSet(op(_, _), base, fun, indices) ==
  \* note that ApalacheFoldSet is accumulating the result in the left argument,
  \* whereas FoldFunction is accumulating the result in the right argument.
  LET Map(y, x) == op(fun[x], y) IN
  __ApalacheFoldSet(Map, base, indices)

===============================================================================
