package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._

abstract class Printer {
  def apply( p_ex : TlaEx ) : String

}

object SimplePrinter extends Printer {

  protected val m_neq    = "\u2260"
  protected val m_and    = "\u2227"
  protected val m_or     = "\u2228"
  protected val m_not    = "\u00AC"
  protected val m_in     = "\u2200"
  protected val m_impl   = "\u21D2"
  protected val m_equiv  = "\u21D4"
  protected val m_le     = "\u2264"
  protected val m_ge     = "\u2265"
  protected val m_forall = "\u2200"
  protected val m_exists = "\u2203"


  override def apply( p_ex : TlaEx ) : String = {
    def str( seq : Seq[TlaEx], sep : String = ", " ) = seq.map( apply ).mkString( sep )

    def opApp( p_ex : TlaEx ) : String = {
      p_ex match {
        case OperEx( TlaSetOper.enumSet, _ ) => apply( p_ex )
        case o : OperEx => "(%s)".format( apply( p_ex ) )
        case _ => apply( p_ex )
      }
    }


    p_ex match {
      case NullEx => "[NULL]"
      case NameEx( name ) => name
      case ValEx( v ) =>
        v match {
          case TlaInt( i ) => i.toString
          case TlaDecimal( d ) => d.toString
          case TlaStr( s ) => s
          case TlaBool( b ) => b.toString
          case _ => ""
        }
      case OperEx( oper : TlaUserOper, args@_* ) => "%s(%s)".format( oper.name, str( args ) )

      case OperEx( TlaOper.eq, a, b ) => "%s = %s".format( opApp( a ), opApp( b ) )
      case OperEx( TlaOper.ne, a, b ) => "%s %s %s".format( opApp( a ), m_neq, opApp( b ) )
      case OperEx( TlaOper.apply, a, b ) => "%s(%s)".format( opApp( a ), opApp( b ) )
      case OperEx( TlaOper.chooseUnbounded, x, p ) =>
        "CHOOSE %s : %s".format( opApp( x ), opApp( p ) )
      case OperEx( TlaOper.chooseBounded, x, s, p ) =>
        "CHOOSE %s %s %s : %s".format( opApp( x ), m_in, opApp( s ), opApp( p ) )

      case OperEx( TlaBoolOper.and, args@_* ) => str( args, " %s ".format( m_and ) )
      case OperEx( TlaBoolOper.or, args@_* ) => str( args, " %s ".format( m_or ) )
      case OperEx( TlaBoolOper.not, p ) => "%s%s".format( m_not, opApp( p ) )
      case OperEx( TlaBoolOper.implies, p, q ) => "%s %s %s".format( opApp( p ), m_impl, opApp( q ) )
      case OperEx( TlaBoolOper.equiv, p, q ) => "%s %s %s".format( opApp( p ), m_equiv, opApp( q ) )
      case OperEx( TlaBoolOper.forall, x, s, p ) =>
        "%s%s %s %s . %s".format( m_forall, opApp( x ), m_in, opApp( s ), opApp( p ) )
      case OperEx( TlaBoolOper.exists, x, s, p ) =>
        "%s%s %s %s . %s".format( m_exists, opApp( x ), m_in, opApp( s ), opApp( p ) )
      case OperEx( TlaBoolOper.forallUnbounded, x, p ) =>
        "%s%s . %s".format( m_forall, opApp( x ), opApp( p ) )
      case OperEx( TlaBoolOper.existsUnbounded, x, p ) =>
        "%s%s . %s".format( m_exists, opApp( x ), opApp( p ) )

      case OperEx( TlaArithOper.sum, args@_* ) => str( args, " + " )
      case OperEx( TlaArithOper.plus, a, b ) => "%s + %s".format( opApp( a ), opApp( b ) )
      case OperEx( TlaArithOper.uminus, a : TlaEx ) => "-%s".format( opApp( a ) )
      case OperEx( TlaArithOper.minus, a, b ) => "%s - %s".format( opApp( a ), opApp( b ) )
      case OperEx( TlaArithOper.prod, args@_* ) => str( args, " * " )
      case OperEx( TlaArithOper.mult, a, b ) => "%s * %s".format( opApp( a ), opApp( b ) )
      case OperEx( TlaArithOper.div, a, b ) => "%s // %s".format( opApp( a ), opApp( b ) )
      case OperEx( TlaArithOper.mod, a, b ) => "%s %% %s".format( opApp( a ), opApp( b ) )
      case OperEx( TlaArithOper.realDiv, a, b ) => "%s / %s".format( opApp( a ), opApp( b ) )
      case OperEx( TlaArithOper.exp, a, b ) => "%s ^ %s".format( opApp( a ), opApp( b ) )
      case OperEx( TlaArithOper.dotdot, a, b ) => "%s .. %s".format( opApp( a ), opApp( b ) )
      case OperEx( TlaArithOper.lt, a, b ) => "%s < %s".format( opApp( a ), opApp( b ) )
      case OperEx( TlaArithOper.gt, a, b ) => "%s > %s".format( opApp( a ), opApp( b ) )
      case OperEx( TlaArithOper.le, a, b ) => "%s %s %s".format( opApp( a ), m_le, opApp( b ) )
      case OperEx( TlaArithOper.ge, a, b ) => "%s %s %s".format( opApp( a ), m_ge, opApp( b ) )


      case _ => ""
    }
  }
}

object FullPrinter extends Printer {
  override def apply( p_ex : TlaEx ) : String = ""
}