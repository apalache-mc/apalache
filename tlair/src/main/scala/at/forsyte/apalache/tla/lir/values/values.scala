package at.forsyte.apalache.tla.lir.values

import at.forsyte.apalache.tla.lir.TlaValue

/**
  * An integer constant (unbounded as in TLA+).
  */
case class TlaInt(value: BigInt) extends TlaValue {
  def isNatural: Boolean = {
    value >= 0
  }
}

/**
  * A decimal constant d_1...d_k.d_k+1...d_m.
  * Since we represent the decimal value with BigDecimal, one should take care of rounding results.
  */
case class TlaDecimal(value: BigDecimal) extends TlaValue

/**
  * A truly real number, not a float.
  * This class is kept for compatibility with TLA+. We do not have an efficient representation for it.
  */
case class TlaReal() extends TlaValue

/**
  * <p>The infinity constant that corresponds to Reals!Infinity.</p>
  *
  * <p>The word "real" in the name merely suggests that this is a constant defined in the Reals module,
  * and should not be understood as an invitation to a philosophical discourse on existence of infinite values :-)</p>
  */
object TlaRealInfinity extends TlaReal

/**
  * A Boolean constant. Efficiently, there are two values: TlaBool(false) and TlaBool(true).
  * We keep the case class and do not introduce objects such as TlaFalse and TlaTrue for consistency with other values.
  */
case class TlaBool(value: Boolean) extends TlaValue

/**
  * A string constant.
  */
case class TlaStr(value: String) extends TlaValue

/**
  * A predefined constant set, e.g., the set of all integers.
  */
abstract class TlaPredefSet() extends TlaValue {
  val name: String
}

/**
  * The standard set of booleans. It should be equal to { FALSE, TRUE }.
  */
object TlaBoolSet extends TlaPredefSet {
  override val name: String = "BOOLEAN"
}

/**
  * The standard set of all strings.
  */
object TlaStrSet extends TlaPredefSet {
  override val name: String = "STRING"
}

/**
  * The standard set of all integers.
  */
object TlaIntSet extends TlaPredefSet {
  override val name: String = "Int"
}

/**
  * The standard set of all naturals, including zero.
  */
object TlaNatSet extends TlaPredefSet {
  override val name: String = "Nat"
}

/**
  * The standard set of all reals.
  */
object TlaRealSet extends TlaPredefSet {
  override val name: String = "Real"
}
