package at.forsyte.apalache.tla.lir.transformations.impl

import at.forsyte.apalache.tla.lir.RecursiveProcessor
import at.forsyte.apalache.tla.lir.transformations.ExprTransformer

// TODO: Igor @ 01.07.2019: we do not need this class.
// The user can simply decorate any recursive function with TransformationFactory.listenTo.
class RecursiveTransformationImpl(transformation : ExprTransformer )
  extends TransformationImpl(
    RecursiveProcessor.transformTlaEx(
      RecursiveProcessor.DefaultFunctions.naturalTermination,
      transformation,
      transformation
    )
  )
