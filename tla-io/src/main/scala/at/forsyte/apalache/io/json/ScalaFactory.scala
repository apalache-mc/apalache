package at.forsyte.apalache.io.json

/**
 * Generates Scala primitives/collections from JSON primitives/arrays.
 * Inverse to JsonFactory, i.e. as{X}( JsonFactory.from{x}(v: X) ) == v, for X = Int/Str/Bool/Traversable
 * @tparam T Any class extending JsonRepresentation
 */
trait ScalaFactory[T <: JsonRepresentation] {
  def asInt(json: T): Int
  def asStr(json: T): String
  def asBool(json: T): Boolean
  def asSeq(json: T): Seq[T]
}
