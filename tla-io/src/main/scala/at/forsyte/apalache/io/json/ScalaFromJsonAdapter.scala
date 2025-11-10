package at.forsyte.apalache.io.json

/**
 * Adapter that extracts Scala primitives/collections from JSON primitives/arrays.
 *
 * This follows the GoF Adapter pattern, converting the interface of JsonRepresentation into Scala primitive types that
 * clients expect.
 *
 * Inverse to ScalaToJsonAdapter, i.e. as{X}(ScalaToJsonAdapter.from{X}(v: X)) == v, for X = Int/Str/Bool/Iterable
 *
 * @tparam T
 *   Any class extending JsonRepresentation
 */
trait ScalaFromJsonAdapter[T <: JsonRepresentation] {
  def asInt(json: T): Int
  def asStr(json: T): String
  def asBool(json: T): Boolean
  def asSeq(json: T): Seq[T]
}
