package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.{ConstT1, StrT1, TlaType1}

import scala.util.matching.Regex

/**
 * Handles the identification of special model value strings. These values are input as strings, but their
 * types (and SMT sorts) are unique and they are incomparable with regular strings of with other
 * model values of a different type.
 *
 * Each model value follows the pattern: `[NAME]_OF_[TYPE]`, where:
 *
 *  - NAME is a unique identifier within the model value type. Its actual value is unimportant.
 *  - TYPE is the type of this particular model value. e.g., a value foo_OF_XYZ has the uninterpreted type XYZ.
 *
 *  Model values that are constructed with different identifiers are not equal to one another.
 *
 *  @author Jure Kukovec
 */
object ModelValueHandler {

  /**
   * The name that is designated for string, in contrast to model values.
   */
  val STRING_TYPE: String = "str"
  private val matchRegex: Regex = raw"([a-zA-Z0-9_]+)_OF_([A-Z_][A-Z0-9_]*)".r

  /**
   * Returns the type of `s`.
   * If `s` follows the pattern for model values, its type is `ConstT1(_)`, otherwise is
   * is a regular string.
   */
  def modelValueOrString(s: String): TlaType1 = {
    typeAndIndex(s).map(_._1).getOrElse(StrT1())
  }

  /**
   * Attempts to extract the type and index from thew pattern. If None, the value `s` is not a model value,
   * but a regular string.
   */
  def typeAndIndex(s: String): Option[(ConstT1, String)] = {
    s match {
      case matchRegex(name, sort) => Some(ConstT1(sort), name)
      case _                      => None
    }
  }

  /**
   * Synthesizes a model value string from its components.
   */
  def construct(typeAndName: (String, String)): String = {
    val tp = typeAndName._1
    val name = typeAndName._2
    s"${name}_OF_$tp"
  }
}
