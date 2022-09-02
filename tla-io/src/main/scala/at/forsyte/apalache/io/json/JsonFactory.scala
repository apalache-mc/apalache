package at.forsyte.apalache.io.json

/**
 * Generates JsonRepresentation objects on demand
 * @tparam R
 *   The class of the value which the JsonRepresentation uses to reprsent JSON
 * @tparam T
 *   Any class extending JsonRepresentation
 */
trait JsonFactory[R, T <: JsonRepresentation[R]] {
  def mkObj(fields: (String, T)*): T
  def fromInt(int: Int): T
  def fromStr(str: String): T
  def fromBool(bool: Boolean): T
  def fromIterable(trv: Iterable[T]): T
}
