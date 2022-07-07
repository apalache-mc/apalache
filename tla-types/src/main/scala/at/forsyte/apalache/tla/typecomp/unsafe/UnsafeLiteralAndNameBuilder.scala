package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.typecheck.ModelValueHandler
import at.forsyte.apalache.tla.typecomp.TBuilderTypeException

/**
 * Scope-unsafe builder for names and literals (IR tree leaves)
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeLiteralAndNameBuilder {

  /** i : Int */
  protected def _int(i: BigInt): TlaEx = ValEx(TlaInt(i))(Typed(IntT1))

  /** s : Str */
  protected def _str(s: String): TlaEx = {
    if (ModelValueHandler.isModelValue(s))
      throw new TBuilderTypeException(
          s"$s represents a value of an uninterpreted sort ${ModelValueHandler.modelValueOrString(s)}, not a string. Use [const] instead."
      )
    ValEx(TlaStr(s))(Typed(StrT1))
  }

  /** b : Bool */
  protected def _bool(b: Boolean): TlaEx = ValEx(TlaBool(b))(Typed(BoolT1))

  /** root_OF_A : A */
  protected def _const(root: String, A: ConstT1): TlaEx = {
    if (ModelValueHandler.isModelValue(root))
      throw new TBuilderTypeException(
          s"Ambiguous uninterpreted literal. $root should be the root name, not the full name (e.g. \"1\", not \"1_OF_A\").")
    val fullStr = ModelValueHandler.construct((A.name, root))
    ValEx(TlaStr(fullStr))(Typed(A))
  }

  /** v : A */
  protected def _constParsed(v: String): TlaEx = {
    if (!ModelValueHandler.isModelValue(v))
      throw new TBuilderTypeException(
          s"$v represents a string, not a value of an uninterpreted sort. Use [str] instead."
      )
    val tt = ModelValueHandler.typeAndIndex(v).get._1
    ValEx(TlaStr(v))(Typed(tt))
  }

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
