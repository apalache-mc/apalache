package at.forsyte.apalache.tla.typecmp.raw

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values._

/**
 * @author
 *   Jure Kukovec
 */
trait RawLeafBuilder {

  protected def _int(i: BigInt): ValEx = ValEx(TlaInt(i))(Typed(IntT1()))

  protected def _str(s: String): ValEx = ValEx(TlaStr(s))(Typed(StrT1()))

  protected def _bool(b: Boolean): ValEx = ValEx(TlaBool(b))(Typed(BoolT1()))

  protected def _booleanSet(): ValEx = ValEx(TlaBoolSet)(Typed(SetT1(BoolT1())))

  protected def _stringSet(): ValEx = ValEx(TlaStrSet)(Typed(SetT1(StrT1())))

  protected def _intSet(): ValEx = ValEx(TlaIntSet)(Typed(SetT1(IntT1())))

  protected def _natSet(): ValEx = ValEx(TlaNatSet)(Typed(SetT1(IntT1())))

  protected def _name(exprName: String, exType: TlaType1): NameEx = NameEx(exprName)(Typed(exType))
}
