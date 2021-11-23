package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.TlaType1Scheme

import scala.collection.immutable.SortedMap

/**
 * A type context assigns poly- or monotypes to names (such as operator names and the names of quantified variables).
 *
 * @param types a map from a name to the assigned typed and universal type variables
 * @author Igor Konnov
 */
class TypeContext(val types: Map[String, TlaType1Scheme]) {

  /**
   * Get the name and the set of universally quantified type variables (as integers) that are associated with the name.
   *
   * @param name a name in the type context
   * @return the associated type and the set of type variables (as integers) that are associated with the name.
   */
  def apply(name: String): TlaType1Scheme = {
    types.get(name) match {
      case Some(pair) => pair
      case None       => throw new IllegalArgumentException(s"No type binding for $name in the type context")
    }
  }
}

object TypeContext {

  /**
   * An empty type context.
   */
  val empty: TypeContext = new TypeContext(Map.empty)

  def apply(namedTypes: (String, TlaType1Scheme)*): TypeContext = {
    new TypeContext(SortedMap(namedTypes: _*))
  }
}
