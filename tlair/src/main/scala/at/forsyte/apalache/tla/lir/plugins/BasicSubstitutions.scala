package at.forsyte.apalache.tla.lir.plugins

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._

/**
  * Created by jkukovec on 12/2/16.
  */
package object BasicSubstitutions {

  def substitute( tlaEx: TlaEx ): TlaEx = {
    def resub( tlaEx : TlaEx ) : TlaEx = {
      tlaEx match{
        case OperEx( o , xs @ _* ) =>
        {
          val newxs = xs.map( substitute )
          if (xs == newxs) tlaEx
          else substitute( OperEx( o, newxs : _* ) )
        }
        case _ => tlaEx

      }
    }

    tlaEx match {
      case OperEx( TlaArithOper.plus, ValEx( TlaInt( a ) ), ValEx( TlaInt( b ) ) ) => ValEx( TlaInt( a + b ) )  // compute arithmetic
      case OperEx( TlaArithOper.minus, ValEx( TlaInt( a ) ), ValEx( TlaInt( b ) ) ) => ValEx( TlaInt( a - b ) ) // -||-

      case OperEx( TlaOper.eq, x, y ) =>
        if (x == y) ValEx( TlaTrue )                                                                            // x = x is TRUE
        else resub( tlaEx )                                                                                     // else check for other subs

      case OperEx( TlaBoolOper.and, x ) => substitute( x )
      case OperEx( TlaBoolOper.and, xs @ _* ) => // NONBASIC, REQUIRES BOOL CHECKING
        if ( xs.contains( ValEx( TlaFalse ) ) )
          ValEx( TlaFalse )
        else OperEx( TlaBoolOper.and, xs.filterNot( x => x == ValEx( TlaTrue ) ).map(substitute):_*)

      case OperEx( TlaBoolOper.or, x ) => substitute( x )
      case OperEx( TlaBoolOper.or, xs @ _* ) => // NONBASIC, REQUIRES BOOL CHECKING
        if ( xs.contains( ValEx( TlaTrue ) ) )
          ValEx( TlaTrue )
        else OperEx( TlaBoolOper.or, xs.filterNot( x => x == ValEx( TlaFalse ) ).map(substitute):_*)

      case _ => resub( tlaEx )
    }
  }

  def performOnEx( f: TlaEx => TlaEx, spec : TlaSpec ) : TlaSpec = {
    new TlaSpec( spec.name,
      spec.declarations.map(
        (x : TlaDecl) => x match{
          case TlaOperDecl( a, b, ex ) => TlaOperDecl( a, b, f( ex ) )
          case x => x
        }
      )
    )
  }

  def sub( spec : TlaSpec ) : TlaSpec = performOnEx( substitute, spec )


}
