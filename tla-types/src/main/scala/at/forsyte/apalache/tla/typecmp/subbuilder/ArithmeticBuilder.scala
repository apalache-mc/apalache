package at.forsyte.apalache.tla.typecmp.subbuilder

import at.forsyte.apalache.tla.typecmp.BuilderWrapper
import at.forsyte.apalache.tla.typecmp.raw.RawArithmeticBuilder
import at.forsyte.apalache.tla.typecmp.BuilderUtil.binaryFromRaw

/**
 * Builder for TlaArithOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ArithmeticBuilder extends RawArithmeticBuilder {

  /** x + y */
  def plus(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_plus)

  /** x - y */
  def minus(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_minus)

  /** -x */
  def uminus(xW: BuilderWrapper): BuilderWrapper = xW.map(_uminus)

  /** x * y */
  def mult(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_mult)

  /** x \div y */
  def div(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_div)

  /** x % y */
  def mod(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_mod)

  /** x^y */
  def exp(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_exp)

  /** x .. y */
  def dotdot(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_dotdot)

  /** x < y */
  def lt(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_lt)

  /** x > y */
  def gt(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_gt)

  /** x <= y */
  def le(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_le)

  /** x >= y */
  def ge(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_ge)
}
