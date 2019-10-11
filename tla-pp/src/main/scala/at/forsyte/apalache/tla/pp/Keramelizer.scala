package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
  * A simplifier from TLA+ to KerA+.
  *
  * To get the idea about KerA+, check the paper at OOPSLA'19: TLA+ Model Checking Made Symbolic.
  *
  * @author Igor Konnov
  */
class Keramelizer(tracker: TransformationTracker) extends TlaExTransformation {
  override def apply(ex: TlaEx): TlaEx = {
    ex
  }
}
