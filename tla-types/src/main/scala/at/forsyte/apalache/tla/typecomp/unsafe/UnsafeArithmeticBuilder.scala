package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaArithOper

/**
 * Type-unsafe builder for TlaArithOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeArithmeticBuilder extends ProtoBuilder {

  /** x + y */
  protected def _plus(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.plus, x, y)

  /** x - y */
  protected def _minus(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.minus, x, y)

  /** -x */
  protected def _uminus(x: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.uminus, x)

  /** x * y */
  protected def _mult(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.mult, x, y)

  /** x \div y */
  protected def _div(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.div, x, y)

  /** x % y */
  protected def _mod(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.mod, x, y)

  /** x^y */
  protected def _exp(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.exp, x, y)

  /** x .. y */
  protected def _dotdot(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.dotdot, x, y)

  /** x < y */
  protected def _lt(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.lt, x, y)

  /** x > y */
  protected def _gt(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.gt, x, y)

  /** x <= y */
  protected def _le(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.le, x, y)

  /** x >= y */
  protected def _ge(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.ge, x, y)
}
