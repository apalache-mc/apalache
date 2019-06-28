package at.forsyte.apalache.tla.assignments.transformations

import at.forsyte.apalache.tla.imp.src.{SourceLocation, SourceStore}
import at.forsyte.apalache.tla.lir.transformations.TransformationInvariant
import at.forsyte.apalache.tla.lir.{RecursiveProcessor, TlaEx}

/**
  * A transformation T is source-preserving, if it maintains the following invariant:
  *
  * \forall e \in Sub(T(X)) . source(e) <= source(X)
  */
sealed case class SourceInvariant( sourceMap : SourceStore )
  extends TransformationInvariant(
    "SourceInvariant",
    {
      case (originalEx, newEx) =>
        def isUnder( ex1 : TlaEx, ex2 : TlaEx ) : Boolean = {
          for {
            loc1 <- sourceMap.find( ex1.ID )
            loc2 <- sourceMap.find( ex2.ID )
          } yield loc1.filename == loc2.filename && loc2.region.contains( loc1.region )
        } getOrElse false // if either ID is absent form the map and the result is None, return false
        RecursiveProcessor.globalTlaExProperty( isUnder( _, originalEx ) )( newEx )
    }
  )