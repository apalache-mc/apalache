package at.forsyte.apalache.tla.assignments.transformations

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.transformations.impl.{RecursiveTransformationImpl, TransformationTrackerImpl, TransformationImpl}
import at.forsyte.apalache.tla.lir.transformations.{ExprTransformer, TransformationListener}

sealed case class UnchengedExplicitTracker(listeners: TransformationListener* )
  extends TransformationTrackerImpl( listeners :_* ) {

  def inSingleton( x : TlaEx ) : TlaEx =
    Builder.in( Builder.prime( x.deepCopy() ), Builder.enumSet( x.deepCopy() ) )

  val OneUnchangedExplicit: ExprTransformer =
    track {
      case OperEx( TlaActionOper.unchanged, arg ) =>

        /** UNCHANGED can be applied either to names or to tuples:
          * UNCHANGED x and UNCHANGED (x,y,...) */
        arg match {
          case OperEx( TlaFunOper.tuple, args@_* ) =>
            Builder.and( args.map( inSingleton ) : _* )
          case NameEx( _ ) => inSingleton( arg )
          case ex => ex
        }
      case ex => ex
    }

  /**
    * Replaces all instances of UNCHANGED with their KERA equivalents
    *
    * Example:
    * UNCHANGED x --> x' \in {x}
    * UNCHANGED (x,...,y) --> x' \in {x} /\ ... /\ y' \in {y}
    *
    */
  val AllUnchangedExplicit: TransformationImpl =
    new RecursiveTransformationImpl( OneUnchangedExplicit )
}
