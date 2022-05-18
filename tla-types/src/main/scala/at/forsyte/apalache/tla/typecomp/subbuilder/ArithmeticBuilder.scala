package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeArithmeticBuilder
import at.forsyte.apalache.tla.typecomp.BuilderUtil.binaryFromUnsafe

/**
 * Type-safe builder for TlaArithOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ArithmeticBuilder extends UnsafeArithmeticBuilder {

  /** x + y */
  def plus(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(_plus)

  /** x - y */
  def minus(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(_minus)

  /** -x */
  def uminus(x: TBuilderInstruction): TBuilderInstruction = x.map(_uminus)

  /** x * y */
  def mult(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(_mult)

  /** x \div y */
  def div(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(_div)

  /** x % y */
  def mod(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(_mod)

  /** x^y */
  def exp(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(_exp)

  /** x .. y */
  def dotdot(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(_dotdot)

  /** x < y */
  def lt(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(_lt)

  /** x > y */
  def gt(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(_gt)

  /** x <= y */
  def le(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(_le)

  /** x >= y */
  def ge(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(_ge)
}
