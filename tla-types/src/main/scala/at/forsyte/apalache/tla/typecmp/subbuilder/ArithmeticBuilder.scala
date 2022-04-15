package at.forsyte.apalache.tla.typecmp.subbuilder

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaArithOper

/**
 * Builder for TlaArithOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ArithmeticBuilder extends ProtoBuilder {
  def plus(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.plus, 2).build(x, y)

  def minus(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.minus, 2).build(x, y)

  def uminus(x: TlaEx): TlaEx = simpleInstruction(TlaArithOper.uminus, 1).build(x)

  def mult(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.mult, 2).build(x, y)

  def div(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.div, 2).build(x, y)

  def mod(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.mod, 2).build(x, y)

  def exp(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.exp, 2).build(x, y)

  def dotdot(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.dotdot, 2).build(x, y)

  def lt(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.lt, 2).build(x, y)

  def gt(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.gt, 2).build(x, y)

  def le(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.le, 2).build(x, y)

  def ge(x: TlaEx, y: TlaEx): TlaEx = simpleInstruction(TlaArithOper.ge, 2).build(x, y)
}
