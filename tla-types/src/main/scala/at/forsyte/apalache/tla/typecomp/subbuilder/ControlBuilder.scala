package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeControlBuilder
import scalaz._

/**
 * Scope-safe builder for TlaSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ControlBuilder extends UnsafeControlBuilder {

  /** {{{IF p THEN A ELSE B}}} */
  def ite(p: TBuilderInstruction, A: TBuilderInstruction, B: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(p, A, B)(_ite)

  /** {{{CASE pairs[0]._1 -> pairs[0]._2 [] ... [] pairs[n]._1 -> pairs[n]._2}}} `pairs` must be nonempty */
  def caseSplit(pairs: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction =
    caseSplitMixed(pairs.flatMap { case (a, b) => Seq(a, b) }: _*)

  /** {{{CASE pairs[0] -> pairs[1] [] ... [] pairs[n-1] -> pairs[n]}}} `pairs` must have even, positive arity */
  def caseSplitMixed(pairs: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(pairs).map(_caseSplitMixed(_: _*))

  /**
   * {{{CASE pairs[0]._1 -> pairs[0]._2 [] ... [] pairs[n]._1 -> pairs[n]._2 [] OTHER -> other}}} `pairs` must be
   * nonempty
   */
  def caseOther(other: TBuilderInstruction, pairs: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction =
    caseOtherMixed(other, pairs.flatMap { case (a, b) => Seq(a, b) }: _*)

  /**
   * {{{CASE pairs[0] -> pairs[1] [] ... [] pairs[n-1] -> pairs[n] [] OTHER -> other}}} `pairs` must have even, positive
   * arity
   */
  def caseOtherMixed(other: TBuilderInstruction, pairs: TBuilderInstruction*): TBuilderInstruction = for {
    otherEx <- other
    pairsExs <- buildSeq(pairs)
  } yield _caseOtherMixed(otherEx, pairsExs: _*)

}
