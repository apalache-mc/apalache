package at.forsyte.apalache.tla.typecmp.subbuilder

import at.forsyte.apalache.tla.typecmp.BuilderWrapper
import at.forsyte.apalache.tla.typecmp.raw.RawArithmeticBuilder

/**
 * Builder for TlaArithOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ArithmeticBuilder extends RawArithmeticBuilder {

  import at.forsyte.apalache.tla.typecmp.BuilderUtil.binaryFromRaw

  def plus(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_plus)

  def minus(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_minus)

  def uminus(xW: BuilderWrapper): BuilderWrapper = xW.map(_uminus)

  def mult(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_mult)

  def div(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_div)

  def mod(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_mod)

  def exp(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_exp)

  def dotdot(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_dotdot)

  def lt(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_lt)

  def gt(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_gt)

  def le(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_le)

  def ge(xW: BuilderWrapper, yW: BuilderWrapper): BuilderWrapper = binaryFromRaw(xW, yW)(_ge)
}
