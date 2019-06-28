package at.forsyte.apalache.tla.assignments.transformations

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, RecursiveProcessor}
import at.forsyte.apalache.tla.lir.transformations.{Transformation, TransformationFactory, TransformationListener}

sealed case class PrimeFactory( vars : Set[String], listeners : TransformationListener* )
  extends TransformationFactory( listeners : _* ) {
  val PrimeOne : Transformation = listenTo {
    case ex@OperEx( TlaActionOper.prime, NameEx( name ) ) =>
      // Do not replace primes twice. This may happen when Init = Inv.
      ex

    case ex@NameEx( name ) if vars.contains( name ) =>
      tla.prime( ex.deepCopy() )

    case ex => ex
  }

  val PrimeAll : Transformation = listenTo {
    // Avoid double-priming
    RecursiveProcessor.transformTlaEx(
      {
        case OperEx( TlaActionOper.prime, _ ) => true
        case _ => false
      },
      RecursiveProcessor.DefaultFunctions.identity,
      PrimeOne.transform
    )
  }
}
