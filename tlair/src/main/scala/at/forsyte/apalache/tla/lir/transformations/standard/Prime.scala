package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaOperDecl}

object Prime {
  private def primeLeaf( vars : Set[String], tracker : TransformationTracker ) : TlaExTransformation =
    tracker.trackEx {
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
  def apply( vars : Set[String], tracker : TransformationTracker ) : TlaExTransformation = tracker.trackEx { ex =>
    val tr = primeLeaf( vars, tracker )
    lazy val self = apply(vars, tracker)
    ex match {
      case LetInEx( body, defs@_* ) =>
        // Transform bodies of all op.defs
        val newDefs = defs map tracker.trackOperDecl { d => d.copy(body = self(d.body)) }
        val newBody = self( body )
        val retEx = if ( defs == newDefs && body == newBody ) ex else LetInEx( newBody, newDefs : _* )
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
