package at.forsyte.apalache.tla.lir

import scala.collection.immutable

package object storage {

  type BodyMapKey = String
  type BodyMapVal = (List[FormalParam], TlaEx)
  type BodyMap = immutable.Map[BodyMapKey, BodyMapVal]
}
