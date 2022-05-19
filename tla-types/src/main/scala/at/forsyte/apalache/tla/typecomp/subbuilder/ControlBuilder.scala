package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeControlBuilder
import scalaz._

/**
 * Type-safe builder for TlaSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ControlBuilder extends UnsafeControlBuilder {

  /** IF p THEN A ELSE B */
  def ite(p: TBuilderInstruction, A: TBuilderInstruction, B: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(p, A, B)(_ite)

  /** CASE p1 -> e1 [] p2 -> e2 [] ... [] pn -> en */
  def caseSplit(pairs: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction =
    caseSplitMixed(pairs.flatMap { case (a, b) => Seq(a, b) }: _*)

  /**
   * Alternate call method, where pairs are passed interleaved
   *
   * @see
   *   caseSplit[[caseSplit(pairs: (TBuilderInstruction, TBuilderInstruction)*)]]
   */
  def caseSplitMixed(pairs: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(pairs).map(_caseSplitMixed(_: _*))

  /** CASE p1 -> e1 [] p2 -> e2 [] ... [] pn -> en [] OTHER -> e */
  def caseOther(other: TBuilderInstruction, pairs: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction =
    caseOtherMixed(other, pairs.flatMap { case (a, b) => Seq(a, b) }: _*)

  /**
   * Alternate call method, where pairs are passed interleaved
   *
   * @see
   *   caseOther[[caseOther(other: TBuilderInstruction, pairs: (TBuilderInstruction, TBuilderInstruction)*)]]
   */
  def caseOtherMixed(other: TBuilderInstruction, pairs: TBuilderInstruction*): TBuilderInstruction = for {
    otherEx <- other
    pairsExs <- buildSeq(pairs)
  } yield _caseOtherMixed(otherEx, pairsExs: _*)

}
