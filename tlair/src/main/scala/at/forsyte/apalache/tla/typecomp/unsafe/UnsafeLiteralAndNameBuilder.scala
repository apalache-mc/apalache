package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.typecomp.TBuilderTypeException
import at.forsyte.apalache.tla.types.ModelValueHandler

/**
 * Scope-unsafe builder for names and literals (IR tree leaves)
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeLiteralAndNameBuilder {

  /** {{{i : Int}}} */
  def int(i: BigInt): TlaEx = ValEx(TlaInt(i))(Typed(IntT1))

  /**
   * {{{s : Str}}}
   * @param s
   *   must be a string literal, not a literal of an uninterpreted sort.
   */
  def str(s: String): TlaEx = {
    if (ModelValueHandler.isModelValue(s))
      throw new TBuilderTypeException(
          s"$s represents a value of an uninterpreted sort ${ModelValueHandler.modelValueOrString(s)}, not a string. Use [const] instead."
      )
    ValEx(TlaStr(s))(Typed(StrT1))
  }

  /** {{{b : Bool}}} */
  def bool(b: Boolean): TlaEx = ValEx(TlaBool(b))(Typed(BoolT1))

  /**
   * {{{root_OF_A : A}}}
   * @param root
   *   must be a string identifier and may not contain the `_OF_` suffix.
   */
  def const(root: String, A: ConstT1): TlaEx = {
    if (ModelValueHandler.isModelValue(root))
      throw new TBuilderTypeException(
          s"Ambiguous uninterpreted literal. $root should be the root name, not the full name (e.g. \"1\", not \"1_OF_A\").")
    val fullStr = ModelValueHandler.construct((A.name, root))
    ValEx(TlaStr(fullStr))(Typed(A))
  }

  /**
   * {{{v : A}}}
   * @param v
   *   must be a literal of an uninterpreted sort, not a string literal.
   */
  def constParsed(v: String): TlaEx = {
    if (!ModelValueHandler.isModelValue(v))
      throw new TBuilderTypeException(
          s"$v represents a string, not a value of an uninterpreted sort. Use [str] instead."
      )
    val tt = ModelValueHandler.typeAndIndex(v).get._1
    ValEx(TlaStr(v))(Typed(tt))
  }

  /** {{{BOOLEAN}}} */
  def booleanSet(): TlaEx = ValEx(TlaBoolSet)(Typed(SetT1(BoolT1)))

  /** {{{STRING}}} */
  def stringSet(): TlaEx = ValEx(TlaStrSet)(Typed(SetT1(StrT1)))

  /** {{{Int}}} */
  def intSet(): TlaEx = ValEx(TlaIntSet)(Typed(SetT1(IntT1)))

  /** {{{Nat}}} */
  def natSet(): TlaEx = ValEx(TlaNatSet)(Typed(SetT1(IntT1)))

  /** {{{exprName: t}}} */
  def name(exprName: String, t: TlaType1): TlaEx = NameEx(exprName)(Typed(t))
}
