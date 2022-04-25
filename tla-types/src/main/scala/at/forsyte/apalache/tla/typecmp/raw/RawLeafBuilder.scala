package at.forsyte.apalache.tla.typecmp.raw

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values._

/**
 * Raw builder for names and literals (IR tree leaves)
 *
 * @author
 *   Jure Kukovec
 */
trait RawLeafBuilder {

  /** i : Int */
  protected def _int(i: BigInt): ValEx = ValEx(TlaInt(i))(Typed(IntT1()))

  /** s : Str */
  protected def _str(s: String): ValEx = ValEx(TlaStr(s))(Typed(StrT1()))

  /** b : Bool */
  protected def _bool(b: Boolean): ValEx = ValEx(TlaBool(b))(Typed(BoolT1()))

  /** BOOLEAN */
  protected def _booleanSet(): ValEx = ValEx(TlaBoolSet)(Typed(SetT1(BoolT1())))

  /** STRING */
  protected def _stringSet(): ValEx = ValEx(TlaStrSet)(Typed(SetT1(StrT1())))

  /** Int */
  protected def _intSet(): ValEx = ValEx(TlaIntSet)(Typed(SetT1(IntT1())))

  /** Nat */
  protected def _natSet(): ValEx = ValEx(TlaNatSet)(Typed(SetT1(IntT1())))

  /** exprName: exType */
  protected def _name(exprName: String, exprType: TlaType1): NameEx = NameEx(exprName)(Typed(exprType))
}
