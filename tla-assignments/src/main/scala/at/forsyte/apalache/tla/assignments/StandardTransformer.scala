package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.db.BodyDB
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.transformations.standard._

/**
  * This object defines the sequence of transformations
  * applied in the assignment pass preprocessing
  */
object StandardTransformer {
  def apply(
             bodyMap : BodyDB,
             tracker : TransformationTracker
           ) : TlaExTransformation = {
    val transformationSequence : Vector[TlaExTransformation] =
      Vector(
        Inline( bodyMap, tracker ),
        ExplicitLetIn( tracker ),
        EqualityAsContainment( tracker ),
        ExplicitUnchanged( tracker )
      )

    {
      ex: TlaEx => transformationSequence.foldLeft( ex ) { (e, t) => t(e) }
    }
  }
}
