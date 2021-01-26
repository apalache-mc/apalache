package at.forsyte.apalache.tla.typecheck

import scala.collection.immutable.SortedMap

/**
  * A type context assigns poly- or monotypes to names (such as operator names and the names of bound variables).
  *
  * @author
  */
class TypeContext(val types: Map[String, TlaType1]) {
  def apply(name: String): TlaType1 = {
    types(name)
  }
}

object TypeContext {
  val empty: TypeContext = new TypeContext(Map.empty)

  def apply(namedTypes: (String, TlaType1)*): TypeContext = {
    new TypeContext(SortedMap(namedTypes: _*))
  }
}
