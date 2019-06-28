package at.forsyte.apalache.tla.assignments.transformations

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.transformations.{RecursiveTransformation, Transformation, TransformationFactory, TransformationListener}

sealed case class UnchengedExplicitFactory( listeners: TransformationListener* )
  extends TransformationFactory( listeners :_* ) {

  def inSingleton( x : TlaEx ) : TlaEx =
    Builder.in( Builder.prime( x.deepCopy() ), Builder.enumSet( x.deepCopy() ) )

  val OneUnchangedExplicit: Transformation =
    listenTo {
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
  val AllUnchangedExplicit: Transformation =
    new RecursiveTransformation( OneUnchangedExplicit )
}
