package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{LetInEx, OperEx}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

object DeepCopy {
  /**
    * Calls deep copy in a way that sets up tracking between every replacement (not just top-level)
    */
  def apply( tracker : TransformationTracker ) : TlaExTransformation = tracker.track { ex =>
    lazy val self = apply( tracker )
    ex match {
      case LetInEx( body, defs@_* ) =>
        // Transform bodies of all op.defs
        val newDefs = defs.map { x =>
          x.copy(
            body = self( x.body )
          )
        }
        LetInEx( self( body ), newDefs : _* )

      case OperEx( op, args@_* ) =>
        OperEx( op, args map self : _* )

      case _ => ex.deepCopy()
    }
  }
}
