package at.forsyte.apalache.tla.lir.cleaner
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.plugins.IDAllocator

/**
  * Created by jkukovec on 11/28/16.
  */
package object Cleaner {
  type IDType = Int
  val allocator : IDAllocator[TlaEx] = new IDAllocator[TlaEx]

  private def process( ex : TlaEx ) : Unit = {
    ex.ID = allocator.allocate( ex )
    ex match {
      case OperEx( oper, args @ _* ) => args.foreach( process )
      case _ => return

    }
  }

  def clean( spec : TlaSpec ) : Unit = {
    spec.declarations.foreach(
      x => x match{
        case TlaOperDecl( _, _, ex) => process( ex )
        case _ => return
      }
    )
  }


}
