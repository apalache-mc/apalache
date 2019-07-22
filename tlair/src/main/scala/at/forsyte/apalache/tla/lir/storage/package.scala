package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.src.SourceLocation

import scala.collection.immutable

package object storage {

  type BodyMapKey = String
  type BodyMapVal = (List[FormalParam], TlaEx)
  type BodyMap = immutable.Map[BodyMapKey, BodyMapVal]

  type SourceMap = immutable.Map[UID, SourceLocation]
}
