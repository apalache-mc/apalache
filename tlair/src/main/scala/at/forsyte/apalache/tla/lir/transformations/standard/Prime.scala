package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.transformations.impl.TransformationTrackerImpl
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationListener}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

sealed case class Prime(vars : Set[String], listeners : TransformationListener* )
  extends TransformationTrackerImpl( listeners : _* ) {
  // Igor @ 01.07.2019: what use is this object?
  val PrimeOne : TlaExTransformation = track {
    case ex@OperEx( TlaActionOper.prime, NameEx( name ) ) =>
      // Do not replace primes twice. This may happen when Init = Inv.
      ex

    case ex@NameEx( name ) if vars.contains( name ) =>
      tla.prime( ex.deepCopy() )

    case ex => ex
  }

  val PrimeAll : TlaExTransformation = track {
    // Igor @ 01.07.2019: I just fail to understand the code with RecursiveProcessor.
    // Replacing recursion in Scala with special classes is like replacing for-loops in C with special functions.
    // One can do that, but there is no reason for that.
    // If you want to avoid duplication between PrimeOne and PrimeAll, use partial functions.

    case ex@OperEx( TlaActionOper.prime, NameEx( name ) ) =>
      // Do not replace primes twice. This may happen when Init = Inv.
      ex

    case ex@NameEx( name ) if vars.contains( name ) =>
      tla.prime( ex.deepCopy() )

    // the following two lines are the difference between PrimeOne and PrimeAll.
    // They can be understood by any Scala programmer, in contrast to the lines that call RecursiveProcessor.
    case OperEx(oper, args @ _*) =>
      OperEx(oper, args map PrimeAll :_*)

    case e => e

    // Avoid double-priming
//    RecursiveProcessor.transformTlaEx(
//      {
//        case OperEx( TlaActionOper.prime, _ ) => true
//        case _ => false
//      },
//      RecursiveProcessor.DefaultFunctions.identity,
//      PrimeOne
//    )
  }
}
