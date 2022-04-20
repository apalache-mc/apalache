package at.forsyte.apalache.tla.typecmp.raw

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values._

/**
 * @author
 *   Jure Kukovec
 */
trait RawLeafBuilder {

  protected def _int(i: BigInt): TlaEx = ValEx(TlaInt(i))(Typed(IntT1()))

  protected def _str(s: String): TlaEx = ValEx(TlaStr(s))(Typed(StrT1()))

  protected def _bool(b: Boolean): TlaEx = ValEx(TlaBool(b))(Typed(BoolT1()))

  protected def _booleanSet(): TlaEx = ValEx(TlaBoolSet)(Typed(SetT1(BoolT1())))

  protected def _stringSet(): TlaEx = ValEx(TlaStrSet)(Typed(SetT1(StrT1())))

  protected def _intSet(): TlaEx = ValEx(TlaIntSet)(Typed(SetT1(IntT1())))

  protected def _natSet(): TlaEx = ValEx(TlaNatSet)(Typed(SetT1(IntT1())))

  protected def _name(exprName: String, exType: TlaType1): TlaEx = NameEx(exprName)(Typed(exType))
}
