package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.TlaType1

import scala.collection.immutable.SortedMap

/**
 * A type context assigns poly- or monotypes to names (such as operator names and the names of bound variables).
 *
 * @param namesInScope the names of the operators in the definition stack
 * @param poolSize     the largest variable index that should be treated as non-free, that is, not universally quantified
 * @param types        a map from a name to the assigned typed and universal type variables
 * @author Igor Konnov
 */
class TypeContext(val namesInScope: Set[String], val poolSize: Int, val types: Map[String, (TlaType1, Set[Int])]) {
  def apply(name: String): (TlaType1, Set[Int]) = {
    types(name)
  }
}

object TypeContext {
  val empty: TypeContext = new TypeContext(Set.empty, -1, Map.empty)

  def apply(namedTypes: (String, (TlaType1, Set[Int]))*): TypeContext = {
    new TypeContext(Set.empty, -1, SortedMap(namedTypes: _*))
  }
}
