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
 * Restriction of a function to a set (must be a subset of the domain).
 *
 * @type: (a -> b, Set(a)) => (a -> b);
 *)
Restrict(__f, __S) == [ __x \in __S |-> __f[__x] ]

(**
 * Range of a function.
 * Note: The image of a set under function f can be defined as
 *       Range(Restrict(f,S)).
 *
 * @type: (a -> b) => Set(b);
 *)
Range(__f) == { __f[__x] : __x \in DOMAIN __f }

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
Inverse(__f, __S, __T) == 
  [__t \in __T |-> CHOOSE __s \in __S: __t \in Range(__f) => __f[__s] = __t]

(**
 * The inverse of a function.
 *
 * @type: (a -> b) => (b -> a);
 *)
AntiFunction(__f) == Inverse(__f, DOMAIN __f, Range(__f))

(**
 * A function is injective iff it maps each element in its domain to a
 * distinct element.
 *
 * This definition is overridden by TLC in the Java class SequencesExt.
 * The operator is overridden by the Java method with the same name.
 *
 * @type: (a -> b) => Bool;
 *)
IsInjective(__f) ==
    \A __a, __b \in DOMAIN __f:
        __f[__a] = __f[__b] => __a = __b

(**
 * Set of injections between two sets.
 *
 * @type: (Set(a), Set(b)) => Set(a -> b);
 *)
Injection(__S, __T) == { __f \in [__S -> __T]: IsInjective(__f) }

(**
 * This operator is not defined in the community modules.
 * As a temporary workaround, we define it globally.
 * TODO: It should be declared as LOCAL, once this issue is fixed:
 * https://github.com/apalache-mc/apalache/issues/1495
 *
 * @type: (Set(a), Set(b), a -> b) => Bool;
 *)
IsSurjective(__S, __T, __f) ==
    \A __t \in __T:
        \E __s \in __S:
            __f[__s] = __t

(**
 * A map is a surjection iff for each element in the range there is some
 * element in the domain that maps to it.
 *
 * @type: (Set(a), Set(b)) => Set(a -> b);
 *)
Surjection(__S, __T) ==
    { __f \in [__S -> __T]: IsSurjective(__S, __T, __f) }

(**
 * A map is a bijection iff it is both an injection and a surjection.
 *
 * @type: (Set(a), Set(b)) => Set(a -> b);
 *)
Bijection(__S, __T) ==
    { __f \in [__S -> __T]: IsSurjective(__S, __T, __f) /\ IsInjective(__f) }

(**
 * Is there an injection between S and T. Apalache defines it only on finite sets.
 *
 * @type: (Set(a), Set(b)) => Bool;
 *)
ExistsInjection(__S, __T)  ==
    Cardinality(__S) <= Cardinality(__T)

(**
 * Is there a surjection between S and T. Apalache defines it only on finite sets.
 *
 * @type: (Set(a), Set(b)) => Bool;
 *)
ExistsSurjection(__S, __T) ==
    Cardinality(__S) >= Cardinality(__T)

(**
 * Is there a bijection between S and T. Apalache defines it only on finite sets.
 *
 * @type: (Set(a), Set(b)) => Bool;
 *)
ExistsBijection(__S, __T)  ==
    Cardinality(__S) = Cardinality(__T)


(**
 * Applies the binary function op on all elements of DOMAIN fun in arbitrary
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
FoldFunction(__op(_, _), __base, __fun) ==
  \* note that ApalacheFoldSet accumulates the result in the left argument,
  \* whereas FoldFunction accumulates the result in the right argument.
  LET __Map(__y, __x) == __op(__fun[__x], __y) IN
  __ApalacheFoldSet(__Map, __base, DOMAIN __fun)


(**
 * Applies the binary function op on the given indices of DOMAIN fun
 * in arbitrary * order starting with op(f[k], base). The resulting
 * function is:
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
FoldFunctionOnSet(__op(_, _), __base, __fun, __indices) ==
  \* note that ApalacheFoldSet accumulates the result in the left argument,
  \* whereas FoldFunction accumulates the result in the right argument.
  LET __Map(__y, __x) == __op(__fun[__x], __y) IN
  __ApalacheFoldSet(__Map, __base, __indices)

===============================================================================
