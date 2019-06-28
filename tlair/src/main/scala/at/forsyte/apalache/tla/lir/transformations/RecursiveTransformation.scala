package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.RecursiveProcessor

class RecursiveTransformation( transformation : Transformation )
  extends Transformation(
    RecursiveProcessor.transformTlaEx(
      RecursiveProcessor.DefaultFunctions.naturalTermination,
      transformation.transform,
      transformation.transform
    )
  )
