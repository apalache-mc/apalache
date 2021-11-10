package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.{ConstT1, StrT1, TlaType1}

import scala.util.matching.Regex

/**
 * Handles the identification of special model value strings. These values are input as strings, but their
 * types (and SMT sorts) are unique and they are incomparable with regular strings of with other
 * model values of a different type.
 *
 * Each model value follows the pattern
 *  [PREFIX]_[TYPE]_[INDEX]
 * where:
 *  - PREFIX is a prefix shared by, and identifying, all model values.
 *  - TYPE is the type of this particular model value. e.g., a value [PREFIX]_XYZ_[INDEX] has the uninterpreted type XYZ
 *  - INDEX is a unique identifier within the model value type. Its actual value is unimportant, however,
 *  model values with different indices are unequal by definition
 */
object ModelValueHandler {
  val PREFIX: String = "uval"
  val STRING_TYPE: String = "str"
  private val matchRegex: Regex = (s"${PREFIX}_([A-Z_][A-Z0-9_]*)_([a-zA-Z0-9]+)").r

  /**
   * Returns the type of `s`.
   * If `s` follows the pattern for model values, its type is `ConstT1(_)`, otherwise is
   * is a regular string.
   */
  def modelValueOrString(s: String): TlaType1 =
    typeAndIndex(s).map(_._1).getOrElse(StrT1())

  /**
   * Attempts to extract the type and index from thew pattern. If None, the value `s` is not a model value,
   * but a regular string.
   */
  def typeAndIndex(s: String): Option[(ConstT1, String)] =
    matchRegex.findFirstMatchIn(s).map(regexMatch => (ConstT1(regexMatch.group(1)), regexMatch.group(2)))

  /**
   * Synthesizes a model value string from its components.
   */
  def construct(typeAndIndex: (String, String)): String =
    s"${PREFIX}_${typeAndIndex._1}_${typeAndIndex._2}"
}
