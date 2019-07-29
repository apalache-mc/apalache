package at.forsyte.apalache.tla.lir.storage

import at.forsyte.apalache.tla.lir.{TlaEx, UID}
import at.forsyte.apalache.tla.lir.src.SourceLocation

/**
  * SourceLocator is used to identify locations in the original .tla specification,
  * from which a given expression, possibly derived from a transformation, originates.
  */
sealed case class SourceLocator(
                                 sourceMap : SourceMap,
                                 changeListener : ChangeListener
                               ) {
  def sourceOf( id : UID ) : Option[SourceLocation] =
    sourceMap.get( changeListener.traceBack( id ) )

  def sourceOf( ex : TlaEx ) : Option[SourceLocation] =
    sourceOf( ex.ID )
}
