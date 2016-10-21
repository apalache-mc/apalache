package at.forsyte.apalache.tla.lir

package values {

  /** an integer value (unbounded as in TLA+) */
  case class TlaInt(value: BigInt) extends TlaValue {
    def isNatural = {
      value >= 0
    }
  }

  /** A decimal value d_1...d_k.d_k+1...d_m.
    * Since we represent the decimal value with BigDecimal, one should take care of rounding results.
    */
  case class TlaDecimal(value: BigDecimal) extends TlaValue

  /** A really real number, not a float.
      For the moment, we don't know what to do about it. */
  case class TlaReal()

  /** a boolean */
  case class TlaBool(value: Boolean) extends TlaValue

  object TlaFalse extends TlaBool(false)

  object TlaTrue extends TlaBool(true)

  /** a function */
  case class TlaFun(domain: TlaSet) extends TlaValue


  /** an abstract set */
  abstract class TlaSet extends TlaValue

  /** an explicit representation of a set */
  case class TlaEnumSet(values: TlaValue*) extends TlaSet

  /** a predefined set, e.g., the set of all integers */
  abstract class TlaBuiltinSet extends TlaSet {
    val name: String
  }

  /** a set of functions, e.g., defined with [S -> T] */
  case class TlaFunSet(elemDomain: TlaSet, elemRange: TlaSet) extends TlaSet


  /** a string */
  case class TlaStr(value: String) extends TlaValue
}
