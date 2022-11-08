package at.forsyte.apalache.io.json

/**
 * A representation of json. The concrete implementation may depend on external json libraries. Defines a toString
 * method, to be used when performing IO.
 */
trait JsonRepresentation {

  /** The type used to represent JSON */
  type Value

  def toString: String
  def getFieldOpt(fieldName: String): Option[this.type]
  def allFieldsOpt: Option[Set[String]]

  /** The value used to represent JSON */
  def value: Value
}
