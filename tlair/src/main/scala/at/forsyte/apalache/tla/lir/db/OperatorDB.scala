package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir._

class OperatorDB extends HashMapDB[EID, (List[FormalParam], EID)] {
  override val m_name = "OperatorDB"

  def params( eid : EID ) : Option[List[FormalParam]] = get( eid ).map( _._1 )

  def arity( eid : EID ) : Option[Integer] = params( eid ).map( _.size )

  def body( eid : EID ) : Option[TlaEx] =
    get( eid ).map(
      x => EquivalenceDB_old.getEx( x._2 ).map( _.deepCopy( identified = false ) )
    ).getOrElse( None )


  def isRecursive( eid : EID ) : Option[Boolean] = {
    val opName = EquivalenceDB_old.getEx( eid ) match {
      case Some( NameEx( name ) ) => name
      case _ => return None
    }

    var recursive : Boolean = false

    def checkForSelf( tlaEx : TlaEx ) : Unit = {
      tlaEx match {
        case NameEx( name ) => if ( name == opName ) recursive = true
        case _ =>
      }
    }

    body( eid ).map(
      { x => SpecHandler.sideeffectEx( x, checkForSelf ); recursive }
    )
  }

}
