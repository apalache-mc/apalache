package at.forsyte.apalache.io.json

/**
 * A representation of json. The concrete implementation may depend on external json libraries.
 * Defines a toString method, to be used when performing IO.
 */
trait JsonRepresentation {
  def toString: String
}
