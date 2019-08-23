package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
  * This object defines the sequence of transformations
  * applied in preprocessing
  */
object StandardTransformer {
  def apply(
             bodyMap : BodyMap,
             tracker : TransformationTracker
           ) : TlaExTransformation = {
    val transformationSequence : Vector[TlaExTransformation] =
      Vector(
        Inline( bodyMap, tracker ),
        ExplicitLetIn( tracker, skip0Arity = false ),
        EqualityAsContainment( tracker ),
        ExplicitUnchanged( tracker ),
        SimplifyRecordAccess( tracker )
      )

    {
      ex: TlaEx => transformationSequence.foldLeft( ex ) {
        (e, t) => t(e)
      }
    }
  }
}
