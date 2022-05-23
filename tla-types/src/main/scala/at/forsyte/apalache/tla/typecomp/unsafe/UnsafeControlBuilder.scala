package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaControlOper

/**
 * Type-unsafe builder for base TlaControlOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeControlBuilder extends ProtoBuilder {

  /** IF p THEN A ELSE B */
  protected def _ite(p: TlaEx, A: TlaEx, B: TlaEx): TlaEx = buildBySignatureLookup(TlaControlOper.ifThenElse, p, A, B)

  // TODO: See comment on map vs mapMixed
  /** CASE p1 -> e1 [] p2 -> e2 [] ... [] pn -> en */
  protected def _caseSplit(pairs: (TlaEx, TlaEx)*): TlaEx = {
    require(pairs.nonEmpty)
    buildBySignatureLookup(TlaControlOper.caseNoOther, pairs.flatMap { case (a, b) => Seq(a, b) }: _*)
  }

  /**
   * Alternate call method, where pairs are passed interleaved
   *
   * @see
   *   _caseSplit[[_caseSplit(pairs: (TlaEx, TlaEx)*)]]
   */
  protected def _caseSplitMixed(pairs: TlaEx*): TlaEx = {
    require(TlaControlOper.caseNoOther.arity.cond(pairs.size))
    buildBySignatureLookup(TlaControlOper.caseNoOther, pairs: _*)
  }

  // TODO: See comment on map vs mapMixed
  /** CASE p1 -> e1 [] p2 -> e2 [] ... [] pn -> en [] OTHER -> e */
  protected def _caseOther(other: TlaEx, pairs: (TlaEx, TlaEx)*): TlaEx = {
    require(pairs.nonEmpty)
    buildBySignatureLookup(TlaControlOper.caseWithOther, other +: pairs.flatMap { case (a, b) => Seq(a, b) }: _*)
  }

  /**
   * Alternate call method, where pairs are passed interleaved
   *
   * @see
   *   _caseOther[[_caseOther(other: TlaEx, pairs: (TlaEx, TlaEx)*)]]
   */
  protected def _caseOtherMixed(other: TlaEx, pairs: TlaEx*): TlaEx = {
    require(TlaControlOper.caseWithOther.arity.cond(1 + pairs.size))
    buildBySignatureLookup(TlaControlOper.caseWithOther, other +: pairs: _*)
  }

}
