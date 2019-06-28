package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.TlaEx

class TransformationFactory( listeners : TransformationListener* ) {
  def listenTo( fn : TlaEx => TlaEx ) : Transformation =
    new Transformation( fn, listeners : _* )
}
