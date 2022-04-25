package at.forsyte.apalache.tla.typecmp.raw

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaArithOper

/**
 * Raw builder for TlaArithOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait RawArithmeticBuilder extends ProtoBuilder {

  /** x + y */
  protected def _plus(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.plus, x, y)

  /** x - y */
  protected def _minus(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.minus, x, y)

  /** -x */
  protected def _uminus(x: TlaEx): TlaEx = simpleInstruction(TlaArithOper.uminus, x)

  /** x * y */
  protected def _mult(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.mult, x, y)

  /** x \div y */
  protected def _div(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.div, x, y)

  /** x % y */
  protected def _mod(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.mod, x, y)

  /** x^y */
  protected def _exp(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.exp, x, y)

  /** x .. y */
  protected def _dotdot(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.dotdot, x, y)

  /** x < y */
  protected def _lt(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.lt, x, y)

  /** x > y */
  protected def _gt(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.gt, x, y)

  /** x <= y */
  protected def _le(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.le, x, y)

  /** x >= y */
  protected def _ge(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.ge, x, y)
}
