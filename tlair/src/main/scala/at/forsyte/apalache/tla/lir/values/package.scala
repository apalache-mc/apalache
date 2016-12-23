package at.forsyte.apalache.tla.lir

package values {

  /** an integer value (unbounded as in TLA+) */
  case class TlaInt(value: BigInt) extends TlaValue {
    def isNatural = {
      value >= 0
    }
  }

  object IntEx{
    def apply( n : BigInt ) : ValEx = ValEx( TlaInt( n ) )
  }

  /** A decimal value d_1...d_k.d_k+1...d_m.
    * Since we represent the decimal value with BigDecimal, one should take care of rounding results.
    */
  case class TlaDecimal(value: BigDecimal) extends TlaValue

  /** A really real number, not a float.
      For the moment, we don't know what to do about it. */
  case class TlaReal() extends TlaValue

  /** a boolean */
  case class TlaBool(value: Boolean) extends TlaValue

  object TlaFalse extends TlaBool(false)

  object TlaTrue extends TlaBool(true)

  /** an abstract set */
  abstract class TlaSet() extends TlaValue

  /** a predefined set, e.g., the set of all integers */
  abstract class TlaPredefSet() extends TlaSet {
    val name: String
  }

  /** A set defined by the user */
  case class TlaUserSet() extends TlaSet

  /** a function */
  case class TlaFun(domain: TlaSet) extends TlaValue

  /** a string */
  case class TlaStr(value: String) extends TlaValue
}
