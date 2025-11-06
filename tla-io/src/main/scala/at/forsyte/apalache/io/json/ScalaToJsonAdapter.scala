package at.forsyte.apalache.io.json

/**
 * Adapter that converts Scala primitives/collections to JSON representation.
 *
 * This follows the GoF Adapter pattern, converting Scala types into the JsonRepresentation
 * interface that clients expect.
 *
 * @tparam T
 *   Any class extending JsonRepresentation
 */
trait ScalaToJsonAdapter[T <: JsonRepresentation] {
  def mkObj(fields: (String, T)*): T
  def fromInt(int: Int): T
  def fromStr(str: String): T
  def fromBool(bool: Boolean): T
  def fromIterable(trv: Iterable[T]): T
}

