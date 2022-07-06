package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeApalacheBuilder
import scalaz.Scalaz._
import scalaz._

/**
 * Type-safe builder for ApalacheOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ApalacheBuilder extends UnsafeApalacheBuilder {

  /** {{{lhs := rhs}}} `lhs` must be a primed variable name. */
  def assign(lhs: TBuilderInstruction, rhs: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(lhs, rhs)(_assign)

  /**
   * {{{Gen(n): t}}}
   *
   * `n` must be > 0
   *
   * Can return any type of expression, so the type must be manually provided, as it cannot be inferred from the
   * argument.
   */
  def gen(n: Int, t: TlaType1): TBuilderInstruction = _gen(n, t).point[TBuilderInternalState]

  /** {{{Skolem(ex)}}} `ex` must be an expression of the shape {{{\E x \in S: P}}} */
  def skolem(ex: TBuilderInstruction): TBuilderInstruction = ex.map(_skolem)

  /** {{{Guess(S)}}} */
  def guess(S: TBuilderInstruction): TBuilderInstruction = S.map(_guess)

  /** {{{Expand(ex)}}} `ex` must be either `SUBSET S` or `[A -> B]` */
  def expand(ex: TBuilderInstruction): TBuilderInstruction = ex.map(_expand)

  /** {{{ConstCard(ex)}}} `ex` must be an expression of the shape {{{Cardinality(S) >= N}}} */
  def constCard(ex: TBuilderInstruction): TBuilderInstruction = ex.map(_constCard)

  /** {{{MkSeq(n, F)}}} `F` must be an expression of the shape {{{LET Op(i) == ... IN Op}}} */
  def mkSeq(len: Int, F: TBuilderInstruction): TBuilderInstruction = F.map(_mkSeq(len, _))

  /** {{{FoldSet(F, v, S)}}} `F` must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}} */
  def foldSet(F: TBuilderInstruction, v: TBuilderInstruction, S: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(F, v, S)(_foldSet)

  /** {{{FoldSeq(F, v, seq)}}} `F` must be an expression of the shape {{{LET Op(a,b) == ... IN Op}}} */
  def foldSeq(F: TBuilderInstruction, v: TBuilderInstruction, seq: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(F, v, seq)(_foldSeq)

  /** {{{SetAsFun(S)}}} */
  def setAsFun(S: TBuilderInstruction): TBuilderInstruction = S.map(_setAsFun)
}
