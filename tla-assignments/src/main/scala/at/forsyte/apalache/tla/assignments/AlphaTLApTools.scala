package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaSetOper}

import scala.collection.immutable.Set

/**
  * Collection of alpha-TLA+ methods.
  */
object AlphaTLApTools{
  private def isCandTemplate( p_ex : TlaEx, p_var : Option[String] ) : Boolean = {
    p_ex match {
      case OperEx(
      TlaSetOper.in,
      OperEx(
      TlaActionOper.prime,
      NameEx( name )
      ),
      _
      ) => p_var.forall( _ == name )
      case _ => false
    }
  }

  /**
    * Returns `true` if `p_ex` is an assignment candidate
    * @param p_ex Input expression
    */
  def isCand( p_ex : TlaEx ) : Boolean = isCandTemplate( p_ex, None )

  /**
    * Returns `true` if `p_ex` is an assignment candidate for the variable `p_var`
    * @param p_var Variable name
    * @param p_ex Input expression
    */
  def isVarCand( p_var : String, p_ex : TlaEx ) : Boolean = isCandTemplate( p_ex, Some( p_var ) )

  /**
    * Returns the set of all primed variables appearing in subformulas of `p_ex`
    * @param p_ex Input expression
    */
  def findPrimes( p_ex : TlaEx ) : Set[String] = {
    p_ex match {
      case OperEx( TlaActionOper.prime, NameEx( name ) ) =>
        Set( name )
      case OperEx( _, args@_* ) =>
        args.map( findPrimes ).fold( Set[String]() ) {
          _ ++ _
        }
      case _ =>
        Set[String]()
    }
  }

}
