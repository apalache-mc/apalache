package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.LetInOper

// Contains methods and classes used in testing/debugging/experimenting
package object aux {

  def aggregate[T](
                    join : (T, T) => T,
                    base : TlaEx => T
                  )
                  ( ex : TlaEx ) : T = {
    val self = aggregate[T]( join, base )( _ )
    ex match {
      case OperEx( letIn : LetInOper, body ) =>
        join(
          self( body ),
          letIn.defs.map( _.body ).map( self ).foldLeft( base( ex ) ) {
            join
          }
        )
      case OperEx( _, args@_* ) => args.map( self ).foldLeft( base( ex ) ) {
        join
      }
      case _ => base(ex)
    }
  }

  def allUidsBelow: TlaEx => Set[UID] = aggregate[Set[UID]](
    _ ++ _,
    ex => Set(ex.ID)
  )
  def uidToExMap: TlaEx => Map[UID,TlaEx] = aggregate[Map[UID,TlaEx]](
    _ ++ _,
    ex => Map(ex.ID -> ex)
  )

}
