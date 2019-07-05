package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.oper.LetInOper
import at.forsyte.apalache.tla.lir.transformations.impl.TransformationImpl
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationListener, TransformationTracker}

object ReplaceFixed {
  def replaceOne(
             replacedEx : TlaEx,
             newEx : TlaEx,
             tracker : TransformationTracker
           ) : TlaExTransformation = tracker.track {
    ex => if ( ex == replacedEx ) newEx else ex
  }

  /**
    * Returns a transformation which replaces every instance of `replacedEx`
    * with an instance of `newEx`
    */
  def apply(
             replacedEx : TlaEx,
             newEx : TlaEx,
             tracker : TransformationTracker
           ) : TlaExTransformation = { ex =>
    val tr = replaceOne( replacedEx, newEx, tracker )
    // No need to call tracker.track again, tr is always called on the top-level expression
    ex match {
      case OperEx( op: LetInOper, body ) =>
        // do something with op.decls
        // ...
        tr( apply( replacedEx, newEx, tracker )(body) )
      case OperEx( op, args@_* ) =>
        val newArgs = args map apply( replacedEx, newEx, tracker )
        val retEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( retEx )
      case _ => tr(ex)
    }
  }
  
}

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