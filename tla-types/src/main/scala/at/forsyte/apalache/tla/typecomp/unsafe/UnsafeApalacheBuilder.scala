package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaInt

/**
 * Type-unsafe builder for ApalacheOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeApalacheBuilder extends ProtoBuilder {

  /** {{{lhs := rhs}}} `lhs` must be a primed variable name. */
  protected def _assign(lhs: TlaEx, rhs: TlaEx): TlaEx = {
    require(lhs match {
      case OperEx(TlaActionOper.prime, _: NameEx) => true
      case _                                      => false
    })
    buildBySignatureLookup(ApalacheOper.assign, lhs, rhs)
  }

  /**
   * {{{Gen(n): t}}}
   *
   * `n` must be > 0
   *
   * Can return any type of expression, so the type must be manually provided, as it cannot be inferred from the
   * argument.
   */
  protected def _gen(n: Int, t: TlaType1): TlaEx = {
    require(n > 0)
    OperEx(ApalacheOper.gen, ValEx(TlaInt(n))(Typed(IntT1)))(Typed(t))
  }

  /** {{{Skolem(ex)}}} `ex` must be an expression of the shape {{{\E x \in S: P}}} */
  protected def _skolem(ex: TlaEx): TlaEx = {
    require(ex match {
      case OperEx(TlaBoolOper.exists, _, _, _) => true
      case _                                   => false
    })
    buildBySignatureLookup(ApalacheOper.skolem, ex)
  }

  /** {{{Guess(S)}}} */
  protected def _guess(S: TlaEx): TlaEx = buildBySignatureLookup(ApalacheOper.guess, S)

  /** {{{Expand(ex)}}} `ex` must be either `SUBSET S` or `[A -> B]` */
  protected def _expand(ex: TlaEx): TlaEx = {
    require(ex match {
      case OperEx(TlaSetOper.powerset, _)  => true
      case OperEx(TlaSetOper.funSet, _, _) => true
      case _                               => false
    })
    buildBySignatureLookup(ApalacheOper.expand, ex)
  }

  /** {{{ConstCard(ex)}}} `ex` must be an expression of the shape {{{Cardinality(S) >= N}}} */
  protected def _constCard(ex: TlaEx): TlaEx = {
    require(ex match {
      case OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, _), ValEx(_: TlaInt)) => true
      case _                                                                                  => false
    })
    buildBySignatureLookup(ApalacheOper.constCard, ex)
  }

  private def isNaryLambda(n: Int)(ex: TlaEx): Boolean = ex match {
    case LetInEx(NameEx(appName), TlaOperDecl(operName, params, _)) => appName == operName && params.size == n
    case _                                                          => false
  }

  /** {{{MkSeq(n, F)}}} `F` must be an expression of the shape {{{LET Op(i) == ... IN Op}}} */
  protected def _mkSeq(len: Int, F: TlaEx): TlaEx = {
    require(isNaryLambda(n = 1)(F))
    buildBySignatureLookup(ApalacheOper.mkSeq, ValEx(TlaInt(len))(Typed(IntT1)), F)
  }

  /** {{{FoldSet(F, v, S)}}} `F` must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}} */
  protected def _foldSet(F: TlaEx, v: TlaEx, S: TlaEx): TlaEx = {
    require(isNaryLambda(n = 2)(F))
    buildBySignatureLookup(ApalacheOper.foldSet, F, v, S)
  }

  /** {{{FoldSeq(F, v, seq)}}} `F` must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}} */
  protected def _foldSeq(F: TlaEx, v: TlaEx, seq: TlaEx): TlaEx = {
    require(isNaryLambda(n = 2)(F))
    buildBySignatureLookup(ApalacheOper.foldSeq, F, v, seq)
  }

  /** {{{SetAsFun(S)}}} */
  protected def _setAsFun(S: TlaEx): TlaEx = buildBySignatureLookup(ApalacheOper.setAsFun, S)
}
