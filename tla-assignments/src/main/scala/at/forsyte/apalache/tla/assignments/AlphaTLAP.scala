package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.TlaFalse

abstract class AlphaEx( ex : TlaEx ) {
  val id : UID = ex.ID
}

sealed case class Star( ex : TlaEx ) extends AlphaEx( ex ) {
//  val deps : Set[Var] = {
//    SpecHandler.bottomUpVal[Set[Var]](
//      ex,
//      _ match {
//        case OperEx( TlaActionOper.prime, NameEx( _ ) ) => true
//        case _ => false
//      },
//      _ match {
//        case OperEx( TlaActionOper.prime, NameEx( n ) ) => Set( n )
//        case _ => Set.empty[Var]
//      },
//      ( _, s ) => s.fold( Set.empty[Var] ) {_ ++ _},
//      Set.empty[Var]
//    )
//    Set.empty[Var] // TODO
//  }

  def getVars(ex: TlaEx): Set[Var] = ex match {
    case OperEx( TlaActionOper.prime, NameEx( n ) ) => Set(n)
    case OperEx(_, args@_*) => {args map getVars}.foldLeft(Set.empty[Var]) { _ ++ _ }
    case _ => Set.empty[Var]
  }

  val deps : Set[Var] = getVars( ex )
}

sealed case class FalseEx( ex : TlaEx ) extends AlphaEx( ex )

sealed case class AsgnEx( ex : OperEx, v : Var, rhs : Star ) extends AlphaEx( ex )

sealed case class AndOr( ex : OperEx, args : AlphaEx* ) extends AlphaEx( ex ) {
  val oper : TlaOper = ex.oper
}

sealed case class Exists( ex : OperEx, boundVar: Star, set : Star, body : AlphaEx ) extends AlphaEx( ex )

sealed case class ITE( ex : OperEx, IF : Star, THEN : AlphaEx, ELSE : AlphaEx ) extends AlphaEx( ex )

object AlphaTransform {
  def apply( ex : TlaEx ) : AlphaEx = ex match {
    case e@OperEx( TlaBoolOper.and | TlaBoolOper.or, args@_* ) =>
      AndOr( e, args map {
        AlphaTransform( _ )
      } : _* )
    case e@OperEx( TlaControlOper.ifThenElse, ifArgs, thenArgs, elseArgs ) =>
      ITE( e, Star( ifArgs ), AlphaTransform( thenArgs ), AlphaTransform( elseArgs ) )
    case e@OperEx( TlaBoolOper.exists, x, set, body ) =>
      Exists( e, Star(x), Star( set ), AlphaTransform( body ) )
    case e@OperEx( TlaSetOper.in, OperEx( TlaActionOper.prime, NameEx( v ) ), rhs ) =>
      AsgnEx( e, v, Star( rhs ) )
    case ValEx( TlaFalse ) => FalseEx( ex )
    case _ => Star( ex )
  }
}

