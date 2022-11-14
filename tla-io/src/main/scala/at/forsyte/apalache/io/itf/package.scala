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

}
