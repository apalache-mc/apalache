package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import at.forsyte.apalache.tla.typecmp.subbuilder.{ArithmeticBuilder, BoolBuilder, LeafBuilder}

/**
 * Builder for TLA+ (TNT) IR expressions.
 *
 * The following guarantees hold for any IR tree successfully generated exclusively via ScopedBuilder methods:
 *   - Typed-ness: All subexpressions will have a Typed(_) tag
 *   - Type correctness:
 *     - All literal expressions will have the correct type, as determined by their value ( 1: Int, "a" : Str, etc.)
 *     - For each operator application expression OperEx(oper, args:_*)(Typed(resultType)), the following holds:
 *       - oper(args:_*) corresponds to some TNT operator with a signature (T1,...,Tn) => T
 *       - There exists a substitution s, such that: s(T1) = typeof(args[1]), ..., s(Tn) = typeof(args[n]) and s(T) = resultType
 *         Example: For e@OperEx(TlaSetOper.union, 1..4, {5}) the subexpressions 1..4, {5} and e will all have types
 *         Set(Int), since TlaSetOper.union corresponds to \\union: (Set(t), Set(t)) => Set(t), and the substitution
 *         required is t -> Int
 *   - Scope correctness: For each variable that appears as free in the IR tree, all instances of that variable will
 *     have the same type. For each sub-tree rooted at an operator, which introduces a bound variable, all instances of
 *     the bound variable will have the same type within the sub-tree. Example: Given \A x \in S: x, if the first x and
 *     S hold the types Int and Set(Int) respectively, while the second x is typed as Bool, the type correctness
 *     requirements imposed by the signature of \A : (t, Set(t), Bool) => Bool are satisfied, but the expression would
 *     not be scope-correct, since x would have to be typed as Int within the scope defined by this \A operator. Thus,
 *     such an expression cannot be constructed by the builder.
 *
 * @author
 *   Jure Kukovec
 */
class ScopedBuilder(val varPool: TypeVarPool) extends BoolBuilder with ArithmeticBuilder with LeafBuilder
