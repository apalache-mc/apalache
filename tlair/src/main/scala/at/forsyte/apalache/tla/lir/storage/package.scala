package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.src.SourceLocation

import scala.collection.immutable

package object storage {

  type BodyMapKey = String
  type BodyMapVal = TlaOperDecl
  type BodyMap = immutable.Map[BodyMapKey, BodyMapVal]

  type SourceMap = immutable.Map[UID, SourceLocation]
  // SourceMap is used to track, for each TlaEx in the original (unmodified) intermediate expression obtained by importing,
  // the section of the input file from which that expression originates.

  // It is used together with a ChangeListener (see SourceLocator) to trace back an arbitrary,
  // post-transformation expression back to a source location.
}
