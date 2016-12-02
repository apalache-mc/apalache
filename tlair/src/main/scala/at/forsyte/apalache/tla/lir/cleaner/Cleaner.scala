package at.forsyte.apalache.tla.lir.cleaner
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import at.forsyte.apalache.tla.lir.plugins.IDAllocator
import at.forsyte.apalache.tla.lir.values.TlaInt

/**
  * Created by jkukovec on 11/28/16.
  */
package object Cleaner {
  type IDType = Int
  val allocator : IDAllocator[TlaEx] = new IDAllocator[TlaEx]

  def reset() : Unit = allocator.reset()

  private def process( ex : TlaEx ) : Unit = {
    ex.ID = allocator.allocate( ex )
    ex match {
      case OperEx( oper, args @ _* ) => args.foreach( process )
      case _ => return

    }
  }

  def clean( spec : TlaSpec ) : TlaSpec = {
    spec.declarations.foreach(
      x => x match{
        case TlaOperDecl( _, _, ex) => process( ex )
      }
    )
    spec
  }

  def transform( tlaEx: TlaEx ): TlaEx = {
    tlaEx match {
      case OperEx( TlaArithOper.plus, ValEx( TlaInt( a ) ), ValEx( TlaInt( b ) ) ) => ValEx( TlaInt( a + b ) )
      case OperEx( o , xs @ _* ) => OperEx( o, xs.map(transform):_*)
      case _ => tlaEx
    }
  }

  def deliterize( spec : TlaSpec ) : TlaSpec = {
    //reset()
    val spc = new TlaSpec( spec.name, spec.declarations.map(
      (x : TlaDecl) => x match{
        case TlaOperDecl( a, b, ex ) => TlaOperDecl( a, b, transform( ex ) )
        case x => x
      }
      )
    )
    clean(spc)
    return spc
  }


}
