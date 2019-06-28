package at.forsyte.apalache.tla.lir.transformations

class TransformationComposition( transformations : Transformation* )
  extends Transformation(
    transformations.foldLeft( _ ) { case (e, tr) => tr( e ) }
  )
