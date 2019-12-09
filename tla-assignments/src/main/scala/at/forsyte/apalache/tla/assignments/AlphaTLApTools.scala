package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaOper}

import scala.collection.immutable.Set

/**
  * Collection of alpha-TLA+ methods.
  */
object AlphaTLApTools{
  private def isCandTemplate( ex : TlaEx, varOpt : Option[String] ) : Boolean = {
    ex match {
      case OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, NameEx( name ) ), _ ) =>
        varOpt.forall( _ == name )
      case _ => false
    }
  }

  /**
    * Returns `true` if `ex` is an assignment candidate
    * @param ex Input expression
    */
  def isCand( ex : TlaEx ) : Boolean = isCandTemplate( ex, None )

  /**
    * Returns `true` if `ex` is an assignment candidate for the variable `varName`
    * @param varName Variable name
    * @param ex Input expression
    */
  def isVarCand( varName : String, ex : TlaEx ) : Boolean = isCandTemplate( ex, Some( varName ) )

  /**
    * Returns the set of all primed variables appearing in subformulas of `ex`
    * @param ex Input expression
    */
  def findPrimes( ex : TlaEx ) : Set[String] = {
    ex match {
      case OperEx( TlaActionOper.prime, NameEx( name ) ) =>
        Set( name )
      case OperEx( _, args@_* ) =>
        args.map( findPrimes ).fold( Set[String]() ) {
          _ ++ _
        }
      case LetInEx( body, defs@_* ) =>
        val primesInDefs = defs map { d => findPrimes(d.body) }
        primesInDefs.foldLeft( findPrimes(body) ){ _ ++ _ }
      case _ =>
        Set[String]()
    }
  }

}
