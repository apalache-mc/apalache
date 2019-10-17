package at.forsyte.apalache.tla

package object types {
  type typeContext = Map[TypeVar, SmtTypeVariable]
  type nameContext = Map[String, SmtTypeVariable]
}
