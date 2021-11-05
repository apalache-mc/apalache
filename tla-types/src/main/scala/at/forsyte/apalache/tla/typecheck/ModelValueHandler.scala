package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.{ConstT1, StrT1, TlaType1}

import scala.util.matching.Regex

object ModelValueHandler {
  private val PREFIX: String = "uval"
  private val matchRegex: Regex = (s"${PREFIX}_([A-Z_][A-Z0-9_]*)_([a-zA-Z0-9]+)").r
  def modelValueOrString(s: String): TlaType1 =
    typeAndIndex(s).map(_._1).getOrElse(StrT1())
  def typeAndIndex(s: String): Option[(ConstT1, String)] =
    matchRegex.findFirstMatchIn(s).map(regexMatch => (ConstT1(regexMatch.group(1)), regexMatch.group(2)))
  def construct(typeAndIndex: (String, String)): String =
    s"${PREFIX}_${typeAndIndex._1}_${typeAndIndex._2}"
}
