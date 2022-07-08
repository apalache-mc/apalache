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

  /**
   * {{{lhs := rhs}}}
   * @param lhs
   *   must be a primed variable name.
   */
  def assign(lhs: TlaEx, rhs: TlaEx): TlaEx = {
    require(lhs match {
          case OperEx(TlaActionOper.prime, _: NameEx) => true
          case _                                      => false
        }, s"lhs = $lhs must be a primed variable name.")
    buildBySignatureLookup(ApalacheOper.assign, lhs, rhs)
  }

  /**
   * {{{Gen(n): t}}}
   *
   * Can return any type of expression, so the type must be manually provided, as it cannot be inferred from the
   * argument.
   *
   * @param n
   *   must be > 0
   */
  def gen(n: Int, t: TlaType1): TlaEx = {
    require(n > 0, s"n = $n must be positive.")
    OperEx(ApalacheOper.gen, ValEx(TlaInt(n))(Typed(IntT1)))(Typed(t))
  }

  /**
   * {{{Skolem(ex)}}}
   * @param ex
   *   must be an expression of the shape {{{\E x \in S: P}}}
   */
  def skolem(ex: TlaEx): TlaEx = {
    require(ex match {
          case OperEx(TlaBoolOper.exists, _, _, _) => true
          case _                                   => false
        }, s"ex = $ex must be an existential.")
    buildBySignatureLookup(ApalacheOper.skolem, ex)
  }

  /** {{{Guess(S)}}} */
  def guess(S: TlaEx): TlaEx = buildBySignatureLookup(ApalacheOper.guess, S)

  /**
   * {{{Expand(ex)}}}
   * @param ex
   *   must be either `SUBSET S` or `[A -> B]`
   */
  def expand(ex: TlaEx): TlaEx = {
    require(ex match {
          case OperEx(TlaSetOper.powerset, _)  => true
          case OperEx(TlaSetOper.funSet, _, _) => true
          case _                               => false
        }, s"ex = $ex must be a powerset or a function set.")
    buildBySignatureLookup(ApalacheOper.expand, ex)
  }

  /**
   * {{{ConstCard(ex)}}}
   * @param ex
   *   must be an expression of the shape {{{Cardinality(S) >= N}}}
   */
  def constCard(ex: TlaEx): TlaEx = {
    require(ex match {
          case OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, _), ValEx(_: TlaInt)) => true
          case _                                                                                  => false
        }, s"ex = $ex must be a cardinality comparison.")
    buildBySignatureLookup(ApalacheOper.constCard, ex)
  }

  private def isNaryPassByName(n: Int)(ex: TlaEx): Boolean = ex match {
    case LetInEx(NameEx(appName), TlaOperDecl(operName, params, _)) => appName == operName && params.size == n
    case _                                                          => false
  }

  /**
   * {{{MkSeq(n, F)}}}
   * @param n
   *   must be > 0
   * @param F
   *   must be an expression of the shape {{{LET Op(i) == ... IN Op}}}
   */
  def mkSeq(n: Int, F: TlaEx): TlaEx = {
    require(n > 0, s"n = $n must be positive.")
    require(isNaryPassByName(n = 1)(F), s"F = $F must a unary operator passed by name.")
    buildBySignatureLookup(ApalacheOper.mkSeq, ValEx(TlaInt(n))(Typed(IntT1)), F)
  }

  /**
   * {{{FoldSet(F, v, S)}}}
   * @param F
   *   must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}}
   */
  def foldSet(F: TlaEx, v: TlaEx, S: TlaEx): TlaEx = {
    require(isNaryPassByName(n = 2)(F), s"F = $F must a binary operator passed by name.")
    buildBySignatureLookup(ApalacheOper.foldSet, F, v, S)
  }

  /**
   * {{{FoldSeq(F, v, seq)}}}
   * @param F
   *   must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}}
   */
  def foldSeq(F: TlaEx, v: TlaEx, seq: TlaEx): TlaEx = {
    require(isNaryPassByName(n = 2)(F), s"F = $F must a binary operator passed by name.")
    buildBySignatureLookup(ApalacheOper.foldSeq, F, v, seq)
  }

  /** {{{SetAsFun(S)}}} */
  def setAsFun(S: TlaEx): TlaEx = buildBySignatureLookup(ApalacheOper.setAsFun, S)
}
