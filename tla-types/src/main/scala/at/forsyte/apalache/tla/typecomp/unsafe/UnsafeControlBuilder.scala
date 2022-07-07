package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaControlOper

/**
 * Scope-unsafe builder for base TlaControlOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
class UnsafeControlBuilder extends ProtoBuilder {

  /** {{{IF p THEN A ELSE B}}} */
  def ite(p: TlaEx, A: TlaEx, B: TlaEx): TlaEx = buildBySignatureLookup(TlaControlOper.ifThenElse, p, A, B)

  /** {{{CASE pairs[0]._1 -> pairs[0]._2 [] ... [] pairs[n]._1 -> pairs[n]._2}}} `pairs` must be nonempty */
  def caseSplit(pairs: (TlaEx, TlaEx)*): TlaEx = {
    require(pairs.nonEmpty)
    buildBySignatureLookup(TlaControlOper.caseNoOther, pairs.flatMap { case (a, b) => Seq(a, b) }: _*)
  }

  /** {{{CASE pairs[0] -> pairs[1] [] ... [] pairs[n-1] -> pairs[n]}}} `pairs` must have even, positive arity */
  def caseSplitMixed(pairs: TlaEx*): TlaEx = {
    require(TlaControlOper.caseNoOther.arity.cond(pairs.size))
    buildBySignatureLookup(TlaControlOper.caseNoOther, pairs: _*)
  }

  /**
   * {{{CASE pairs[0]._1 -> pairs[0]._2 [] ... [] pairs[n]._1 -> pairs[n]._2 [] OTHER -> other}}} `pairs` must be
   * nonempty
   */
  def caseOther(other: TlaEx, pairs: (TlaEx, TlaEx)*): TlaEx = {
    require(pairs.nonEmpty)
    buildBySignatureLookup(TlaControlOper.caseWithOther, other +: pairs.flatMap { case (a, b) => Seq(a, b) }: _*)
  }

  /**
   * {{{CASE pairs[0] -> pairs[1] [] ... [] pairs[n-1] -> pairs[n] [] OTHER -> other}}} `pairs` must have even, positive
   * arity
   */
  def caseOtherMixed(other: TlaEx, pairs: TlaEx*): TlaEx = {
    require(TlaControlOper.caseWithOther.arity.cond(1 + pairs.size))
    buildBySignatureLookup(TlaControlOper.caseWithOther, other +: pairs: _*)
  }

}
