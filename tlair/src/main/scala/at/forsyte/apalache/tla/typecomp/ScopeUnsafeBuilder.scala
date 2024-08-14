package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.BuilderUtil.{getAllBound, getAllUsed, markAsBound}
import at.forsyte.apalache.tla.typecomp.subbuilder._
import at.forsyte.apalache.tla.typecomp.unsafe.{UnsafeActionBuilder, UnsafeApalacheBuilder, UnsafeApalacheInternalBuilder, UnsafeArithmeticBuilder, UnsafeBaseBuilder, UnsafeBoolBuilder, UnsafeControlBuilder, UnsafeFiniteSetBuilder, UnsafeFunBuilder, UnsafeLiteralAndNameBuilder, UnsafeSeqBuilder, UnsafeSetBuilder, UnsafeTemporalBuilder, UnsafeVariantBuilder}
import scalaz.Scalaz._

/**
 * Scope-unsafe Builder for TLA+ (TNT) IR expressions.
 *
 * The following guarantees hold for any IR tree successfully generated exclusively via ScopeUnsafeBuilder methods:
 *   - Typed-ness: All subexpressions will have a `Typed(_)` tag
 *   - Type correctness:
 *     - All literal expressions will have the correct type, as determined by their value ( `1: Int`, `"a" : Str`, etc.)
 *     - For each operator application expression `OperEx(oper, args:_*)(Typed(resultType))`, the following holds:
 *       - `oper(args:_*)` corresponds to some TNT operator with a signature `(T1,...,Tn) => T`
 *       - There exists some substitution `s`, such that: `s(T1) = typeof(args[1]), ..., s(Tn) = typeof(args[n])` and
 *         `s(T) = resultType`. Example: For `e @ OperEx(TlaSetOper.union, 1..4, {5})` the subexpressions `1..4, {5}`
 *         and `e` will all have types `Set(Int)`, since
 *         [[at.forsyte.apalache.tla.lir.oper.TlaSetOper.union TlaSetOper.union]] corresponds to `\union`, which has the
 *         signature `(Set(t), Set(t)) => Set(t)`, and the substitution required is `t -> Int`.
 *
 * If `strict` mode is enabled, the builder rejects inputs for ApalacheOper methods, which do not adhere to the method
 * requirements ("... must be ..."), even if their types are correct. If `strict` mode is disabled, the builder should
 * allow for the construction of any expression, which may be present in a freshly parsed specification (i.e. before
 * preprocessing).
 *
 * @author
 *   Jure Kukovec
 * @param strict
 *   If true, performs method requirement checks
 */
class ScopeUnsafeBuilder(val strict: Boolean = true)
  extends UnsafeBaseBuilder with UnsafeBoolBuilder with UnsafeArithmeticBuilder with UnsafeSetBuilder
    with UnsafeFiniteSetBuilder with UnsafeSeqBuilder with UnsafeActionBuilder with UnsafeFunBuilder
    with UnsafeControlBuilder with UnsafeTemporalBuilder with UnsafeApalacheInternalBuilder
    with UnsafeApalacheBuilder with UnsafeVariantBuilder with UnsafeLiteralAndNameBuilder {

  ////////////////////
  // HYBRID METHODS //
  ////////////////////

  /** x' = y */
  def primeEq(x: TlaEx, y: TlaEx): TlaEx = eql(prime(x), y)

  import ParamUtil._

  def param(name: String, tt: TlaType1): TypedParam = ParamUtil.param(name, tt)

  /** opName(params[1],...,params[n]) == body */
  def decl(opName: String, body: TlaEx, params: TypedParam*): TlaOperDecl = {
    params.foreach(validateParamType)
    TlaOperDecl(opName, params.map(_._1).toList, body)(
      Typed(
        OperT1(params.map { _._2 }, body.typeTag.asTlaType1())
      )
    )
  }

  /**
   * Creates an expression of the form
   *
   * {{{
   * LET uniqueName(p1,...,pn) == body IN uniqueName
   * }}}
   *
   * Matching the representation of LAMBDAs produced by SANY.
   *
   * NOTE: It is left up to the caller to ensure `uniqueName` is unique.
   *
   * Failure to ensure uniqueness of names can lead to name collisions in case lambdas are nested.
   */
  def lambda(uniqueName: String, body: TlaEx, params: TypedParam*): TlaEx = {
    params.foreach(validateParamType)
    val paramTypes = params.map(_._2)
    val operType = OperT1(paramTypes, body.typeTag.asTlaType1())
    letIn(name(uniqueName, operType), decl(uniqueName, body, params: _*))
  }

  /** {{{LET decl(...) = ... IN body}}} */
  def letIn(body: TlaEx, decl: TlaOperDecl): TlaEx =
    LetInEx(body, decl)(body.typeTag)

  /**
   * {{{LET F_1(a_1^1,...,a_{n_1}^1) == X_1 F_2(a_1^2,...,b_{n_2}^2) == X_2 ... F_N(a_1^N,...,z_{n_N}^N) == X_N IN e}}}
   * is equivalently translated to
   * {{{
   *   LET F_1(a_1^1,...,a_{n_1}^1) == X_1 IN
   *   LET F_2(a_1^2,...,b_{n_2}^2) == X_2 IN
   *   ...
   *   LET F_N(a_1^N,...,z_{n_N}^N) == X_N IN
   *   e
   * }}}
   */
  def letIn(body: TlaEx, decls: TlaOperDecl*): TlaEx = {
    require(decls.nonEmpty, "decls must be nonempty.")
    decls.foldRight(body) { case (decl, partial) =>
      letIn(partial, decl)
    }
  }

  /**
   * [f EXCEPT ![a1] = e1, ![a2] = e2 ... ![an] = en]
   *
   * Is equivalent to {{{[[f EXCEPT ![a1] = e1] EXCEPT ![a2] = e2] EXCEPT ... ![an] = en]}}}
   */
  def exceptMany(
                  f: TlaEx,
                  args: (TlaEx, TlaEx)*): TlaEx = {
    require(args.nonEmpty, s"args must be nonempty.")
    args.foldLeft(f) { case (fn, (ai, ei)) =>
      except(fn, ai, ei)
    }
  }

  /**
   * A name expression referring to the TlaVarDecl
   */
  def varDeclAsNameEx(decl: TlaVarDecl): TlaEx = name(decl.name, decl.typeTag.asTlaType1())
}
