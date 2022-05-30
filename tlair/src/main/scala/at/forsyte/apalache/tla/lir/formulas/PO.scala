package at.forsyte.apalache.tla.lir.formulas

/**
 * PO defines constructors for partial orders over uninterpreted sorts.
 *
 * @author
 *   Jure Kukovec
 */
object PO {
  sealed case class LtGeneric(lhs: Term, rhs: Term) extends Booleans.BoolExpr
}
