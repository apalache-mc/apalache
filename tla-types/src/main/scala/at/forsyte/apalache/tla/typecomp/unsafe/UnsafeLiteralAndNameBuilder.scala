package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values._

/**
 * Type-unsafe builder for names and literals (IR tree leaves)
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeLiteralAndNameBuilder {

  /** i : Int */
  protected def _int(i: BigInt): TlaEx = ValEx(TlaInt(i))(Typed(IntT1))

  /** s : Str */
  protected def _str(s: String): TlaEx = ValEx(TlaStr(s))(Typed(StrT1))

  /** b : Bool */
  protected def _bool(b: Boolean): TlaEx = ValEx(TlaBool(b))(Typed(BoolT1))

  /** BOOLEAN */
  protected def _booleanSet(): TlaEx = ValEx(TlaBoolSet)(Typed(SetT1(BoolT1)))

  /** STRING */
  protected def _stringSet(): TlaEx = ValEx(TlaStrSet)(Typed(SetT1(StrT1)))

  /** Int */
  protected def _intSet(): TlaEx = ValEx(TlaIntSet)(Typed(SetT1(IntT1)))

  /** Nat */
  protected def _natSet(): TlaEx = ValEx(TlaNatSet)(Typed(SetT1(IntT1)))

  /** exprName: exType */
  protected def _name(exprName: String, exprType: TlaType1): TlaEx = NameEx(exprName)(Typed(exprType))
}
