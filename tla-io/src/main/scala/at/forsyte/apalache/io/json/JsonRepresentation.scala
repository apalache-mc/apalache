package at.forsyte.apalache.io.json

/**
 * A representation of json. The concrete implementation may depend on external json libraries. Defines a toString
 * method, to be used when performing IO.
 *
 * @tparam T
 *   The class of the value which the JsonRepresentation uses to reprsent JSON
 */
trait JsonRepresentation[T] {
  def toString: String
  def getFieldOpt(fieldName: String): Option[this.type]

  /** The value used to represent JSON */
  def value: T
}
