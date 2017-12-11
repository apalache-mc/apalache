package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper._

object WarningDetector {
  type Warnings = Set[UID]

  def nestedAssignments( p_ex : TlaEx ) : Warnings = {

    val default = Set[UID]()

    def leafJudge( ex : TlaEx ) : Boolean = {
      ex match {
        case OperEx( oper, _* ) =>
          oper match {
            case TlaBoolOper.and |
                 TlaBoolOper.or |
                 TlaSetOper.in |
                 TlaBoolOper.exists => false
            case _ => true
          }
        case _ => true
      }
    }

    def leafFun( ex : TlaEx ) : Warnings = {
      ex match {
        case OperEx( TlaSetOper.in, OperEx( TlaActionOper.prime, NameEx( _ ) ), set ) =>
          leafFun( set ) + ex.ID
        case OperEx( _, args@_* ) =>
          args.map( leafFun ).fold( Set[UID]() )( _ ++ _ )
        case _ =>
          Set[UID]()
      }
    }

    def parentFun( ex : TlaEx, childVals : Seq[Warnings] ) : Warnings = {
      childVals.fold( Set[UID]() )( _ ++ _ )
    }

    SpecHandler.bottomUpVal( p_ex, leafJudge, leafFun, parentFun, default )
  }

  def apply( p_ex : TlaEx ) : Warnings = {
    nestedAssignments( p_ex )
  }

}
