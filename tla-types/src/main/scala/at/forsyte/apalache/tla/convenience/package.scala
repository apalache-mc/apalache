package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.{OperParam, TlaType1, TypeTag}

import scala.language.implicitConversions

/**
 * Package containing a ScopedBuilder instance
 *
 * @author
 *   Jure Kukovec
 */
package object convenience {

  import typecomp._

  implicit def tagAsTlaType1: TypeTag => TlaType1 = TlaType1.fromTypeTag

  val tla = new ScopedBuilder

  implicit def simpleParamFromString(s: String): OperParam = OperParam(s, 0)
  implicit def operaParamFromPair(pa: (String, Int)): OperParam = OperParam(pa._1, pa._2)

  implicit def fromBInt(i: BigInt): TBuilderInstruction = tla.int(i)
  implicit def fromInt(i: Int): TBuilderInstruction = tla.int(i)
  implicit def fromStr(s: String): TBuilderInstruction = tla.str(s)
  implicit def fromBool(b: Boolean): TBuilderInstruction = tla.bool(b)

}
