package at.forsyte.apalache.io

/**
 * @author
 *   Jure Kukovec
 */
package object itf {
  abstract class ItfError(val m: String) extends Exception(m)
  case class ItfFormatError(override val m: String) extends ItfError(m)
  case class ItfContentError(override val m: String) extends ItfError(m)
  case class MultipleErrors(errors: Seq[ItfError]) extends ItfError(
          s"Multiple errors: ${errors.map { e => s"${e.getClass.toString}: ${e.m}" }.mkString("\n")}"
      )

  val META_FIELD: String = "#meta"
  val VAR_TYPES_FIELD: String = "varTypes"
  val VARS_FIELD: String = "vars"
  val PARAMS_FIELD: String = "params"
  val STATES_FIELD: String = "states"
  val DESCRIPTION_FIELD: String = "description"
  val FORMAT_FIELD: String = "format"
  val FORMAT_DESCRIPTION_FIELD: String = "format-description"
  val VARIABLES_TO_EXPRESSIONS_FIELD: String = "variables-to-expressions"
  val INDEX_FIELD: String = "index"
  val TAG_FIELD: String = "tag"
  val VALUE_FIELD: String = "value"
  val BIG_INT_FIELD: String = "#bigint"
  val TUP_FIELD: String = "#tup"
  val SET_FIELD: String = "#set"
  val MAP_FIELD: String = "#map"
  val UNSERIALIZABLE_FIELD: String = "#unserializable"

}
