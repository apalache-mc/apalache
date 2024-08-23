package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaArithOper

/**
 * Scope-unsafe builder for TlaArithOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeArithmeticBuilder extends ProtoBuilder {

  /** {{{x + y}}} */
  def plus(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.plus, x, y)

  /** {{{x - y}}} */
  def minus(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.minus, x, y)

  /** {{{-x}}} */
  def uminus(x: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.uminus, x)

  /** {{{x * y}}} */
  def mult(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.mult, x, y)

  /** {{{x \div y}}} */
  def div(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.div, x, y)

  /** {{{x % y}}} */
  def mod(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.mod, x, y)

  /** {{{x^y}}} */
  def exp(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.exp, x, y)

  /** {{{x .. y}}} */
  def dotdot(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.dotdot, x, y)

  /** {{{x < y}}} */
  def lt(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.lt, x, y)

  /** {{{x > y}}} */
  def gt(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.gt, x, y)

  /** {{{x <= y}}} */
  def le(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.le, x, y)

  /** {{{x >= y}}} */
  def ge(x: TlaEx, y: TlaEx): TlaEx = buildBySignatureLookup(TlaArithOper.ge, x, y)
}
