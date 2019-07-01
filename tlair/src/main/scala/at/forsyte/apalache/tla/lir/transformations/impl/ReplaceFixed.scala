package at.forsyte.apalache.tla.lir.transformations.impl

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.transformations.TransformationListener

/**
  * A Transformation where every instance of `replacedEx` is replaced by an instance of `newEx`
  */
// TODO: Igor @ 01.07.2019: this class has really no value. It is just new TransformationImpl(e: TlaEx => e, listeners).
// TODO: remove?
sealed case class ReplaceFixed(
                                replacedEx : TlaEx,
                                newEx : TlaEx,
                                listeners : TransformationListener*
                              )
  extends TransformationImpl(
    ex => if ( ex == replacedEx ) newEx.deepCopy() else ex,
    listeners : _*
  )
