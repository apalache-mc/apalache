package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{LetInOper, TlaActionOper}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

object Prime {
  private def primeLeaf( vars : Set[String], tracker : TransformationTracker ) : TlaExTransformation =
    tracker.track {
      case ex@NameEx( name ) if vars.contains( name ) =>
        tla.prime( ex )

      case ex => ex
    }

  /**
    * Returns a transformation which primes all unprimed variables from `vars` appearing in a given expression
    *
    * Example:
    *
    * a' + b > 0 --> a' + b' > 0
    */
  def apply( vars : Set[String], tracker : TransformationTracker ) : TlaExTransformation = tracker.track { ex =>
    val tr = primeLeaf( vars, tracker )
    lazy val self = apply(vars, tracker)
    // No need to call tracker.track again, tr is always called on the top-level expression
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
      case ex@OperEx( TlaActionOper.prime, NameEx( _ ) ) =>
        // Do not prime expressions which are already primed. This may happen when Init = Inv.
        tr(ex)
      case ex@OperEx( op, args@_* ) =>
        val newArgs = args map self
        val retEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( retEx )
      case _ => tr( ex )
    }
  }
}
