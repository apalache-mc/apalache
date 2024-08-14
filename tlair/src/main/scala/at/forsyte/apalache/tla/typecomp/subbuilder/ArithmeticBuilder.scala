package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeArithmeticBuilder
import at.forsyte.apalache.tla.typecomp.BuilderUtil.binaryFromUnsafe

/**
 * Scope-safe builder for TlaArithOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ArithmeticBuilder {
  private val unsafeBuilder = new UnsafeArithmeticBuilder {}

  /** {{{x + y}}} */
  def plus(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, y)(unsafeBuilder.plus)

  /** {{{x - y}}} */
  def minus(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, y)(unsafeBuilder.minus)

  /** {{{-x}}} */
  def uminus(x: TBuilderInstruction): TBuilderInstruction = x.map(unsafeBuilder.uminus)

  /** {{{x * y}}} */
  def mult(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, y)(unsafeBuilder.mult)

  /** {{{x \div y}}} */
  def div(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, y)(unsafeBuilder.div)

  /** {{{x % y}}} */
  def mod(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, y)(unsafeBuilder.mod)

  /** {{{x^y}}} */
  def exp(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, y)(unsafeBuilder.exp)

  /** {{{x .. y}}} */
  def dotdot(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, y)(unsafeBuilder.dotdot)

  /** {{{x < y}}} */
  def lt(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(unsafeBuilder.lt)

  /** {{{x > y}}} */
  def gt(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(unsafeBuilder.gt)

  /** {{{x <= y}}} */
  def le(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(unsafeBuilder.le)

  /** {{{x >= y}}} */
  def ge(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(x, y)(unsafeBuilder.ge)
}
