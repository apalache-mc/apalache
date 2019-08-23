package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.transformations.standard._

/**
  * This object defines the sequence of transformations
  * applied in the assignment pass preprocessing
  */
object StandardTransformer {
  def apply(
             bodyMap : BodyMap,
             tracker : TransformationTracker
           ) : TlaExTransformation = {
    val transformationSequence : Vector[TlaExTransformation] =
      Vector(
//        InlineAndExplicitLetIn( bodyMap, tracker ),
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
