package at.forsyte.apalache.io.json

/**
 * Generates JsonRepresentation objects on demand
 * @tparam T Any class extending JsonRepresentation
 */
trait JsonFactory[T <: JsonRepresentation] {
  def mkObj(fields: (String, T)*): T
  def fromInt(int: Int): T
  def fromStr(str: String): T
  def fromBool(bool: Boolean): T
  def fromTraversable(trv: Traversable[T]): T
}
