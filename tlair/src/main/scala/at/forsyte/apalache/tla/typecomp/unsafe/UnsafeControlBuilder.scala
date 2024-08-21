package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaControlOper

/**
 * Scope-unsafe builder for base TlaControlOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeControlBuilder extends ProtoBuilder {

  /** {{{IF p THEN A ELSE B}}} */
  def ite(p: TlaEx, A: TlaEx, B: TlaEx): TlaEx = buildBySignatureLookup(TlaControlOper.ifThenElse, p, A, B)

  /**
   * {{{CASE pairs[0]._1 -> pairs[0]._2 [] ... [] pairs[n]._1 -> pairs[n]._2}}}
   * @param pairs
   *   must be nonempty
   */
  def caseSplit(pairs: (TlaEx, TlaEx)*): TlaEx = {
    require(pairs.nonEmpty, s"pairs must be nonempty.")
    buildBySignatureLookup(TlaControlOper.caseNoOther, pairs.flatMap { case (a, b) => Seq(a, b) }: _*)
  }

  /**
   * {{{CASE pairs[0] -> pairs[1] [] ... [] pairs[n-1] -> pairs[n]}}}
   * @param pairs
   *   must have even, positive arity
   */
  def caseSplitMixed(pairs: TlaEx*): TlaEx = {
    require(TlaControlOper.caseNoOther.arity.cond(pairs.size),
        s"Expected pairs to have even, positive arity, found $pairs.")
    buildBySignatureLookup(TlaControlOper.caseNoOther, pairs: _*)
  }

  /**
   * {{{CASE pairs[0]._1 -> pairs[0]._2 [] ... [] pairs[n]._1 -> pairs[n]._2 [] OTHER -> other}}}
   * @param pairs
   *   must be nonempty
   */
  def caseOther(other: TlaEx, pairs: (TlaEx, TlaEx)*): TlaEx = {
    require(pairs.nonEmpty, s"pairs must be nonempty.")
    buildBySignatureLookup(TlaControlOper.caseWithOther, other +: pairs.flatMap { case (a, b) => Seq(a, b) }: _*)
  }

  /**
   * {{{CASE pairs[0] -> pairs[1] [] ... [] pairs[n-1] -> pairs[n] [] OTHER -> other}}}
   * @param pairs
   *   must have even, positive arity
   */
  def caseOtherMixed(other: TlaEx, pairs: TlaEx*): TlaEx = {
    require(TlaControlOper.caseWithOther.arity.cond(1 + pairs.size),
        s"Expected pairs to have even, positive arity, found $pairs.")
    buildBySignatureLookup(TlaControlOper.caseWithOther, other +: pairs: _*)
  }

}
