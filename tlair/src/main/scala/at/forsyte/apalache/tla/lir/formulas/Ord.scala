package at.forsyte.apalache.tla.lir.formulas

import at.forsyte.apalache.tla.lir.formulas.EUF.UninterpretedLiteral
import at.forsyte.apalache.tla.lir.{ConstT1, IntT1, TypeTag, Typed}

/**
 * Ord defines constructors for partial/total orders.
 *
 * @author
 *   Jure Kukovec
 */
object Ord {
  // Unlike the integer Lt, LtUninterpreted is used when integer arithmetic is disabled and
  // integers are encoded as an uninterpreted sort with a total order.
  sealed case class LtUninterpreted(lhs: Term, rhs: Term) extends Booleans.BoolExpr

  def intToUninterpLit(i: BigInt): UninterpretedLiteral = UninterpretedLiteral(s"$i", Sort.intOrderSort)
  def intTagCorrection(tag: TypeTag): TypeTag = tag match {
    case Typed(IntT1) => Typed(ConstT1(Sort.intAsUninterpretedOrderedSortName))
    case _            => tag
  }
}
