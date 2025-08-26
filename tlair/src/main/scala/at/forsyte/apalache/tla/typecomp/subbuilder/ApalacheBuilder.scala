package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeApalacheBuilder
import scalaz._

/**
 * Scope-safe builder for ApalacheOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ApalacheBuilder {
  val strict: Boolean
  // UnsafeApalacheBuilder is a trait with a parameter `strict`, so we create a class here to instantiate it
  private case class ApalacheBuilderU(strict: Boolean) extends UnsafeApalacheBuilder
  private val unsafeBuilder = ApalacheBuilderU(strict)

  /**
   * {{{lhs := rhs}}}
   * @param lhs
   *   must be a primed variable name.
   */
  def assign(lhs: TBuilderInstruction, rhs: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(lhs, rhs)(unsafeBuilder.assign)

  /**
   * {{{Gen(boundEx): returnType}}}
   *
   * Produce a value generator, given a bound expression and the expected return type.
   *
   * @param boundEx
   *   a bound on the number of generated expressions; it must be reducible to a constant expression
   * @param returnType
   *   the return type of the produced expression
   */
  def gen(boundEx: TBuilderInstruction, returnType: TlaType1): TBuilderInstruction = {
    boundEx.map(unsafeBuilder.gen(_, returnType))
  }

  /**
   * {{{Repeat(F, N, x): t}}}
   * @param n
   *   must be a nonnegative constant expression
   * @param F
   *   must be an expression of the shape {{{LET Op(i) == ... IN Op}}}
   */
  def repeat(F: TBuilderInstruction, n: BigInt, x: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(F, x)(unsafeBuilder.repeat(_, n, _))

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
   * {{{MkSeq(n, F)}}}
   * @param n
   *   must be a nonnegative constant expression
   * @param F
   *   must be an expression of the shape {{{LET Op(i) == ... IN Op}}}
   */
  def mkSeqConst(n: TBuilderInstruction, F: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(n, F)(unsafeBuilder.mkSeqConst)

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
