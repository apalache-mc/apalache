package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.{ConstT1, StrT1, TlaType1}

object ModelValueHandler {
  private val PREFIX = "uval"
  def modelValueOrString(s: String): TlaType1 = {
    // e.g. "PREFIX_UT_0"
    val matchRegex = (s"${PREFIX}_([A-Z_][A-Z0-9_]*)_([a-zA-Z0-9]+)").r
    matchRegex.findFirstMatchIn(s).map(regexMatch => ConstT1(regexMatch.group(1))).getOrElse(StrT1())
  }
}
