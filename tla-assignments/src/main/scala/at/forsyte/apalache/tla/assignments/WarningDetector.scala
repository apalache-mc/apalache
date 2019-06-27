package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper._

abstract class Warning{
  def message : String
  override def toString : String = message

  def isTrivial : Boolean = false
}
case class NoWarning() extends Warning{
  override def message : String = "No warnings to report."
  override def isTrivial : Boolean = true
}
case class NestedAssignmentWarning( p_warnings : Set[UID] ) extends Warning{
  require( p_warnings.nonEmpty )
  override def message : String = {
    ("Warning: The following terms satisfy the structure of potential assignment candidates, " +
      "but will not be considered due to their nesting: %s").format( p_warnings.mkString( ", " ) )
  }
}

case class AggregateWarning( p_warnings : Warning* ) extends Warning{
  override def message : String = {
    if( isTrivial )
      NoWarning().message
    else
      p_warnings.withFilter( _ != NoWarning() ).map( _.message).mkString( "\n" )
  }

  override def isTrivial : Boolean = p_warnings.forall( _.isTrivial )
}

object WarningDetector {
  type NestedWarningSet = Set[UID]

  def nestedAssignments( p_ex : TlaEx ) : Warning = {

    val default = Set[UID]()

    def leafJudge( ex : TlaEx ) : Boolean = {
      ex match {
        case OperEx( oper, _* ) =>
          oper match {
            case TlaBoolOper.and |
                 TlaBoolOper.or |
                 TlaSetOper.in |
                 TlaBoolOper.exists |
                 TlaControlOper.ifThenElse => false
            case _ => true
          }
        case _ => true
      }
    }

    def leafFun( ex : TlaEx ) : NestedWarningSet = {
      ex match {
        case OperEx( TlaSetOper.in, OperEx( TlaActionOper.prime, NameEx( _ ) ), set ) =>
          leafFun( set ) + ex.ID
        case OperEx( _, args@_* ) =>
          args.map( leafFun ).fold( Set[UID]() )( _ ++ _ )
        case _ =>
          Set[UID]()
      }
    }

    def parentFun( ex : TlaEx, childVals : Traversable[NestedWarningSet] ) : NestedWarningSet = {
      childVals.fold( Set[UID]() )( _ ++ _ )
    }

    /**
      * NOTE: RETHINK HOW RP IS CALLED, SINCE THIS IS A REWRITE TO MATCH THE FORMAT OF
      * SpecHandler.bottomUpVal
      **/
    val warningSet = RecursiveProcessor.computeFromTlaEx[NestedWarningSet](
      leafJudge,
      leafFun,
      _ => default,
      parentFun
    )( p_ex )
    if( warningSet.isEmpty ) NoWarning() else NestedAssignmentWarning( warningSet )
  }

  def apply( p_ex : TlaEx ) : Warning = {
    val nestedWarnings = nestedAssignments( p_ex )

    AggregateWarning( nestedWarnings )
  }

}
