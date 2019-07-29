package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{LetInOper, TlaActionOper, TlaFunOper}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

object ExplicitUnchanged {

  protected[lir] def inSingleton( x : TlaEx ) : TlaEx =
    // potentially violates UID uniqueness, both "copies" of x have the same UID
    Builder.in( Builder.prime( x ), Builder.enumSet( x ) )

  private def unchangedExplicitLeaf( tracker : TransformationTracker ) : TlaExTransformation =
    tracker.track {
      case OperEx( TlaActionOper.unchanged, arg ) =>
        val singletonTr = tracker.track( inSingleton )

        /** UNCHANGED can be applied either to names or to tuples:
          * UNCHANGED x and UNCHANGED (x,y,...) */
        arg match {
          case OperEx( TlaFunOper.tuple, args@_* ) =>
            Builder.and( args.map( singletonTr ) : _* )
          case NameEx( _ ) => singletonTr( arg )
          case ex => ex
        }
      case ex => ex
    }

  /**
    * Returns a transformation which replaces all instances of UNCHANGED with their KERA equivalents
    *
    * Example:
    * UNCHANGED x --> x' \in {x}
    * UNCHANGED (x,...,y) --> x' \in {x} /\ ... /\ y' \in {y}
    *
    */
  def apply( tracker : TransformationTracker ) : TlaExTransformation = tracker.track { ex =>
    val tr = unchangedExplicitLeaf( tracker )
    lazy val self = apply( tracker )
    ex match {
      case OperEx( op : LetInOper, body ) =>
        // Transform bodies of all op.defs
        val replacedOperDecls = op.defs.map { x =>
          x.copy(
            body = self( x.body )
          )
        }

        val newOp = new LetInOper( replacedOperDecls )
        val newBody = self( body )
        val retEx = if ( op == newOp && body == newBody ) ex else OperEx( newOp, newBody )

        tr( retEx )
      case ex@OperEx( op, args@_* ) =>
        val newArgs = args map self
        val retEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( retEx )
      case _ => tr( ex )
    }
  }

}
