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
  protected def _plus(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.plus, 2).build(x, y)

  protected def _minus(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.minus, 2).build(x, y)

  protected def _uminus(x: TlaEx): TlaEx = simpleInstruction(TlaArithOper.uminus, 1).build(x)

  protected def _mult(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.mult, 2).build(x, y)

  protected def _div(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.div, 2).build(x, y)

  protected def _mod(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.mod, 2).build(x, y)

  protected def _exp(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.exp, 2).build(x, y)

  protected def _dotdot(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.dotdot, 2).build(x, y)

  protected def _lt(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.lt, 2).build(x, y)

  protected def _gt(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.gt, 2).build(x, y)

  protected def _le(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.le, 2).build(x, y)

  protected def _ge(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.ge, 2).build(x, y)
}
