package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeApalacheBuilder
import scalaz.Scalaz._
import scalaz._

/**
 * Scope-safe builder for ApalacheOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ApalacheBuilder {
  val strict: Boolean
  private val unsafeBuilder = new UnsafeApalacheBuilder(strict)

  /**
   * {{{lhs := rhs}}}
   * @param lhs
   *   must be a primed variable name.
   */
  def assign(lhs: TBuilderInstruction, rhs: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(lhs, rhs)(unsafeBuilder.assign)

  /**
   * {{{Gen(n): t}}}
   *
   * Can return any type of expression, so the type must be manually provided, as it cannot be inferred from the
   * argument.
   *
   * @param n
   *   must be positive
   */
  def gen(n: BigInt, t: TlaType1): TBuilderInstruction = unsafeBuilder.gen(n, t).point[TBuilderInternalState]

  /**
   * {{{Skolem(ex)}}}
   * @param ex
   *   must be an expression of the shape {{{\E x \in S: P}}}
   */
  def skolem(ex: TBuilderInstruction): TBuilderInstruction = ex.map(unsafeBuilder.skolem)

  /** {{{Guess(S)}}} */
  def guess(S: TBuilderInstruction): TBuilderInstruction = S.map(unsafeBuilder.guess)

  /**
   * {{{Expand(ex)}}}
   * @param ex
   *   must be either `SUBSET S` or `[A -> B]`
   */
  def expand(ex: TBuilderInstruction): TBuilderInstruction = ex.map(unsafeBuilder.expand)

  /**
   * {{{ConstCard(ex)}}}
   * @param ex
   *   must be an expression of the shape {{{Cardinality(S) >= N}}}
   */
  def constCard(ex: TBuilderInstruction): TBuilderInstruction = ex.map(unsafeBuilder.constCard)

  /**
   * {{{MkSeq(n, F)}}}
   * @param n
   *   must be nonnegative
   * @param F
   *   must be an expression of the shape {{{LET Op(i) == ... IN Op}}}
   */
  def mkSeq(n: BigInt, F: TBuilderInstruction): TBuilderInstruction = F.map(unsafeBuilder.mkSeq(n, _))

  /**
   * {{{FoldSet(F, v, S)}}}
   * @param F
   *   must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}}
   */
  def foldSet(F: TBuilderInstruction, v: TBuilderInstruction, S: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(F, v, S)(unsafeBuilder.foldSet)

  /**
   * {{{FoldSeq(F, v, seq)}}}
   * @param F
   *   must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}}
   */
  def foldSeq(F: TBuilderInstruction, v: TBuilderInstruction, seq: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(F, v, seq)(unsafeBuilder.foldSeq)

  /** {{{SetAsFun(S)}}} */
  def setAsFun(S: TBuilderInstruction): TBuilderInstruction = S.map(unsafeBuilder.setAsFun)
}
