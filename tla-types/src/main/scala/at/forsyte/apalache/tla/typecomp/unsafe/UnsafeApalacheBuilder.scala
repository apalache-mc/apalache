package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaInt

/**
 * Scope-unsafe builder for ApalacheOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
class UnsafeApalacheBuilder extends ProtoBuilder {

  /** {{{lhs := rhs}}} `lhs` must be a primed variable name. */
  def assign(lhs: TlaEx, rhs: TlaEx): TlaEx = {
    require(lhs match {
      case OperEx(TlaActionOper.prime, _: NameEx) => true
      case _                                      => false
    })
    buildBySignatureLookup(ApalacheOper.assign, lhs, rhs)
  }

  /**
   * {{{Gen(n): t}}} `n` must be > 0
   *
   * Can return any type of expression, so the type must be manually provided, as it cannot be inferred from the
   * argument.
   */
  def gen(n: Int, t: TlaType1): TlaEx = {
    require(n > 0)
    OperEx(ApalacheOper.gen, ValEx(TlaInt(n))(Typed(IntT1)))(Typed(t))
  }

  /** {{{Skolem(ex)}}} `ex` must be an expression of the shape {{{\E x \in S: P}}} */
  def skolem(ex: TlaEx): TlaEx = {
    require(ex match {
      case OperEx(TlaBoolOper.exists, _, _, _) => true
      case _                                   => false
    })
    buildBySignatureLookup(ApalacheOper.skolem, ex)
  }

  /** {{{Guess(S)}}} */
  def guess(S: TlaEx): TlaEx = buildBySignatureLookup(ApalacheOper.guess, S)

  /** {{{Expand(ex)}}} `ex` must be either `SUBSET S` or `[A -> B]` */
  def expand(ex: TlaEx): TlaEx = {
    require(ex match {
      case OperEx(TlaSetOper.powerset, _)  => true
      case OperEx(TlaSetOper.funSet, _, _) => true
      case _                               => false
    })
    buildBySignatureLookup(ApalacheOper.expand, ex)
  }

  /** {{{ConstCard(ex)}}} `ex` must be an expression of the shape {{{Cardinality(S) >= N}}} */
  def constCard(ex: TlaEx): TlaEx = {
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
  def mkSeq(len: Int, F: TlaEx): TlaEx = {
    require(isNaryLambda(n = 1)(F))
    buildBySignatureLookup(ApalacheOper.mkSeq, ValEx(TlaInt(len))(Typed(IntT1)), F)
  }

  /** {{{FoldSet(F, v, S)}}} `F` must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}} */
  def foldSet(F: TlaEx, v: TlaEx, S: TlaEx): TlaEx = {
    require(isNaryLambda(n = 2)(F))
    buildBySignatureLookup(ApalacheOper.foldSet, F, v, S)
  }

  /** {{{FoldSeq(F, v, seq)}}} `F` must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}} */
  def foldSeq(F: TlaEx, v: TlaEx, seq: TlaEx): TlaEx = {
    require(isNaryLambda(n = 2)(F))
    buildBySignatureLookup(ApalacheOper.foldSeq, F, v, seq)
  }

  /** {{{SetAsFun(S)}}} */
  def setAsFun(S: TlaEx): TlaEx = buildBySignatureLookup(ApalacheOper.setAsFun, S)
}
