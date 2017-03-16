package at.forsyte.apalache.tla.lir.values

import at.forsyte.apalache.tla.lir.{TlaValue, ValEx}

/** an integer value (unbounded as in TLA+) */
case class TlaInt(value: BigInt) extends TlaValue {
  def isNatural: Boolean = {
    value >= 0
  }
}

// TODO: do we want to have a less ad hoc solution, e.g., an object with all handy constructors?
object IntEx {
  def apply(n: BigInt): ValEx = ValEx(TlaInt(n))
}

/** A decimal value d_1...d_k.d_k+1...d_m.
  * Since we represent the decimal value with BigDecimal, one should take care of rounding results.
  */
case class TlaDecimal(value: BigDecimal) extends TlaValue

/** A really real number, not a float.
  * For the moment, we don't know what to do about it. */
case class TlaReal() extends TlaValue

/**
  * <p>The infinity constant that corresponds to Reals!Infinity.</p>
  *
  * <p>The word "real" in the name merely suggests that this is a constant defined in the Reals module,
  * and should not be understood as an invitation to a philosophical discourse on existence of infinite values :-)</p>
  */
object TlaRealInfinity extends TlaReal

/** a boolean */
case class TlaBool(value: Boolean) extends TlaValue

object TlaFalse extends TlaBool(false)

object TlaTrue extends TlaBool(true)

/** a string */
case class TlaStr(value: String) extends TlaValue

/** an abstract set */
abstract class TlaSet() extends TlaValue

/** a predefined set, e.g., the set of all integers */
abstract class TlaPredefSet() extends TlaSet {
  val name: String
}

/**
  * A set defined by the user.
  *
  * FIXME: Apparently, we do not need this class, as the only way to define a set is to use
  * an operator... This is already type information, which should be inferred by a type analysis.
  */
case class TlaUserSet() extends TlaSet

/**
  * A function.
  *
  * FIXME: It is not clear, why we need this object at all, as all functions are created with operators.
  */
case class TlaFun(domain: TlaSet) extends TlaValue
