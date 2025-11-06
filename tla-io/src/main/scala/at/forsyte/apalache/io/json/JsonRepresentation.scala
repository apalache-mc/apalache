package at.forsyte.apalache.io.json

/**
 * A representation of json. The concrete implementation may depend on external json libraries. Defines a toString
 * method, to be used when performing IO.
 */
trait JsonRepresentation {
  /** The type used to represent JSON */
  type Value

  /** A pretty-printed string representation of the JSON object */
  def toString: String

  /**
   * If `this` represents a JSON object defining a field `fieldName : val`, the method returns a Some(_), containing the
   * representation of `val`, otherwise (if `this` is not an object or if it does not define a `fieldName` field)
   * returns None.
   * @param fieldName
   *   the name of the field to be retrieved
   * @return
   *   an option containing the field value representation
   */
  def getFieldOpt(fieldName: String): Option[this.type]

  /**
   * If `this` represents a JSON object, returns the set of all field names defined in the object. Otherwise, returns
   * None.
   */
  def allFieldsOpt: Option[Set[String]]

  /** The value used to represent JSON */
  def value: Value
}
