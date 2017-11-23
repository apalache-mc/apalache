package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.temporal.TlaTempOper
import at.forsyte.apalache.tla.lir.values._

abstract class Printer {
  def apply( p_ex : TlaEx ) : String

}

object SimplePrinter extends Printer {

  val m_neq       = "\u2260"
  val m_and       = "\u2227"
  val m_or        = "\u2228"
  val m_not       = "\u00AC"
  val m_in        = "\u2208"
  val m_notin     = "\u2209"
  val m_impl      = "\u21D2"
  val m_equiv     = "\u21D4"
  val m_le        = "\u2264"
  val m_ge        = "\u2265"
  val m_forall    = "\u2200"
  val m_exists    = "\u2203"
  val m_cdot      = "\u22C5"
  val m_box       = "\u2610"
  val m_diamond   = "\u22C4"
  val m_rarrow    = "\u2192"
  val m_ring      = "\u2218"
  val m_guarantee = "\u2945"
  val m_leadsto   = "\u21DD"
  val m_mapto     = "\u21A6"
  val m_cap       = "\u2229"
  val m_cup       = "\u222A"
  val m_subset    = "\u2282"
  val m_subseteq  = "\u2286"
  val m_supset    = "\u2283"
  val m_supseteq  = "\u2287"

  def pad( s : String ) : String = " %s ".format( s )


  override def apply( p_ex : TlaEx ) : String = {
    def mapMk( seq : Seq[TlaEx],
               sep : String = ", ",
               fn : TlaEx => String
             ) = seq.map( fn ).mkString( sep )

    def str( seq : Seq[TlaEx],
             sep : String = ", "
           ) = mapMk( seq, sep, apply )

    def opAppStr( seq : Seq[TlaEx],
                  sep : String = ", "
                ) = mapMk( seq, sep, opApp )

    def groupMapMk( seq : Seq[TlaEx],
                    n : Int,
                    pattern : String,
                    sep : String,
                    fn : TlaEx => String
                  ) = seq.grouped( n ).toSeq.map( s => pattern.format( s.map( fn ) : _* ) ).mkString( sep )

    def strPattern( seq : Seq[TlaEx],
                    n : Int,
                    pattern : String,
                    sep : String
                  ) : String = groupMapMk( seq, n, pattern, sep, apply )

    def opAppPattern( seq : Seq[TlaEx],
                      n : Int,
                      pattern : String,
                      sep : String
                    ) : String = groupMapMk( seq, n, pattern, sep, opApp )

    def opAppStrPairs( seq : Seq[TlaEx],
                       mid : String = pad( m_rarrow ),
                       sep : String = pad( m_box )
                     ) : String =
      opAppPattern( seq, 2, "%%s%s%%s".format( mid ), sep )
    //      seq.grouped( 2 ).toSeq.map( s => s.map( apply ).mkString( mid ) ).mkString( sep )

    def opApp( p_ex : TlaEx ) : String = {
      p_ex match {
        //        case OperEx( oper, args@_* ) =>
        //          oper match {
        //            case (
        //              TlaBoolOper.and |
        //              TlaBoolOper.or |
        //              TlaArithOper.sum |
        //              TlaArithOper.prod |
        //
        //              ) if ( args.size > 1 ) => "(%s)".format( apply( p_ex ) )
        //            case _ => apply( p_ex )
        //          }
        case OperEx( TlaSetOper.enumSet, _ ) => apply( p_ex )
        case OperEx( _, args@_* ) if args.size > 1 => "(%s)".format( apply( p_ex ) )
        case _ => apply( p_ex )
      }
    }


    def mkApp( formatString : String, args : TlaEx* ) = formatString.format( args.map( apply ) : _* )

    def mkOpApp( formatString : String, args : TlaEx* ) = formatString.format( args.map( opApp ) : _* )


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

      case OperEx( oper, args@_* ) =>
        oper match {
          case TlaOper.eq => mkOpApp( "%s = %s", args : _* )
          case TlaOper.ne => mkOpApp( "%%s %s %%s".format( m_neq ), args : _* )
          case TlaOper.apply => ( if ( args.size > 1 ) "%s(%s)" else "%s" ).format( opApp( args.head ), str( args.tail ) )
          case TlaOper.chooseUnbounded => mkOpApp( "CHOOSE %s : %s", args : _* )
          case TlaOper.chooseBounded => mkOpApp( "CHOOSE %%s %s %%s : %%s".format( m_in ), args : _* )

          case TlaBoolOper.and => opAppStr( args, " %s ".format( m_and ) )
          case TlaBoolOper.or => opAppStr( args, " %s ".format( m_or ) )
          case TlaBoolOper.not => mkOpApp( "%s%%s".format( m_not ), args : _* )
          case TlaBoolOper.implies => mkOpApp( "%%s %s %%s".format( m_impl ), args : _* )
          case TlaBoolOper.equiv => mkOpApp( "%%s %s %%s".format( m_equiv ), args : _* )
          case TlaBoolOper.forall => mkOpApp( "%s%%s %s %%s . %%s".format( m_forall, m_in ), args : _* )
          case TlaBoolOper.exists => mkOpApp( "%s%%s %s %%s . %%s".format( m_exists, m_in ), args : _* )
          case TlaBoolOper.forallUnbounded => mkOpApp( "%s%%s . %%s".format( m_forall ), args : _* )
          case TlaBoolOper.existsUnbounded => mkOpApp( "%s%%s . %%s".format( m_exists ), args : _* )

          case TlaArithOper.sum => opAppStr( args, " + " )
          case TlaArithOper.plus => mkOpApp( "%s + %s", args : _* )
          case TlaArithOper.uminus => mkOpApp( "-%s", args : _* )
          case TlaArithOper.minus => mkOpApp( "%s - %s", args : _* )
          case TlaArithOper.prod => opAppStr( args, " * " )
          case TlaArithOper.mult => mkOpApp( "%s * %s", args : _* )
          case TlaArithOper.div => mkOpApp( "%s // %s", args : _* )
          case TlaArithOper.mod => mkOpApp( "%s %% %s", args : _* )
          case TlaArithOper.realDiv => mkOpApp( "%s / %s", args : _* )
          case TlaArithOper.exp => mkOpApp( "%s ^ %s", args : _* )
          case TlaArithOper.dotdot => mkOpApp( "%s .. %s", args : _* )
          case TlaArithOper.lt => mkOpApp( "%s < %s", args : _* )
          case TlaArithOper.gt => mkOpApp( "%s > %s", args : _* )
          case TlaArithOper.le => mkOpApp( "%%s %s %%s".format( m_le ), args : _* )
          case TlaArithOper.ge => mkOpApp( "%%s %s %%s".format( m_ge ), args : _* )

          case TlaActionOper.prime => mkOpApp( "%s'", args : _* )
          case TlaActionOper.stutter => mkOpApp( "[%s]_%s", args : _* )
          case TlaActionOper.nostutter => mkOpApp( "<%s>_%s", args : _* )
          case TlaActionOper.enabled => mkOpApp( "ENABLED %s", args : _* )
          case TlaActionOper.unchanged => mkOpApp( "UNCHANGED %s", args : _* )
          case TlaActionOper.composition => mkOpApp( "%%s %s %%s".format( m_cdot ), args : _* )

          case TlaControlOper.caseNoOther => "CASE %s".format( opAppStrPairs( args ) )
          case TlaControlOper.caseWithOther => "CASE %s %s OTHER %s %s".format( opAppStrPairs( args.tail ), m_box, m_rarrow, args.head )
          case TlaControlOper.ifThenElse => mkOpApp( "IF %s THEN %s ELSE %s", args : _* )

          case TlaTempOper.AA => mkOpApp( "[%s]%%s . %%s".format( m_forall ), args : _* )
          case TlaTempOper.box => mkOpApp( "%s%%s".format( m_box ), args : _* )
          case TlaTempOper.diamond => mkOpApp( "%s%%s".format( m_diamond ), args : _* )
          case TlaTempOper.EE => mkOpApp( "[%s]%%s . %%s".format( m_exists ), args : _* )
          case TlaTempOper.guarantees => mkOpApp( "%%s %s %%s".format( m_guarantee ), args : _* )
          case TlaTempOper.leadsTo => mkOpApp( "%%s %s %%s".format( m_leadsto ), args : _* )
          case TlaTempOper.strongFairness => mkApp( "SF[%s](%s)", args : _* )
          case TlaTempOper.weakFairness => mkApp( "WF[%s](%s)", args : _* )

          case TlaFiniteSetOper.cardinality => mkApp( "Cardinality(%s)", args : _* )
          case TlaFiniteSetOper.isFiniteSet => mkApp( "IsFiniteSet(%s)", args : _* )

          case TlaFunOper.app => "%s[%s]".format( opApp( args.head ), apply( args.tail.head ) )
          case TlaFunOper.domain => mkOpApp( "DOMAIN %s", args : _* )
          case TlaFunOper.enum => "[%s]".format( opAppStrPairs( args, pad( m_mapto ), ", " ) )
          case TlaFunOper.except => "[%s EXCEPT %s]".format( apply( args.head ), opAppPattern( args.tail, 2, "![%s] = %s", ", " ) )
          case TlaFunOper.funDef => "[%s %s %s]".format( opAppStrPairs( args.tail, pad( m_in ), ", " ), m_mapto, apply( args.head ) )
          case TlaFunOper.tuple => "(%s)".format( str( args ) )

          case TlaSeqOper.append => "Append(%s)".format( str( args ) )
          case TlaSeqOper.concat => mkOpApp( "%%s %s %%s".format( m_ring ), args : _* )
          case TlaSeqOper.head => mkApp( "Head(%s)", args : _* )
          case TlaSeqOper.tail => mkApp( "Tail(%s)", args : _* )
          case TlaSeqOper.len => mkApp( "Len(%s)", args : _* )

          case TlaSetOper.enumSet => "{%s}".format( str( args ) )
          case TlaSetOper.in => mkOpApp( "%%s %s %%s".format( m_in ), args : _* )
          case TlaSetOper.notin => mkOpApp( "%%s %s %%s".format( m_notin ), args : _* )
          case TlaSetOper.cap => mkOpApp( "%%s %s %%s".format( m_cap ), args : _* )
          case TlaSetOper.cup => mkOpApp( "%%s %s %%s".format( m_cup ), args : _* )

            /* TODO */

          case TlaSetOper.filter => mkOpApp( "", args : _* )
          case TlaSetOper.funSet => mkOpApp( "", args : _* )
          case TlaSetOper.map => mkOpApp( "", args : _* )
          case TlaSetOper.powerset => mkOpApp( "", args : _* )
          case TlaSetOper.recSet => mkOpApp( "", args : _* )
          case TlaSetOper.seqSet => mkOpApp( "", args : _* )
          case TlaSetOper.setminus => mkOpApp( "", args : _* )
          case TlaSetOper.subseteq => mkOpApp( "", args : _* )
          case TlaSetOper.subsetProper => mkOpApp( "", args : _* )
          case TlaSetOper.supseteq => mkOpApp( "", args : _* )
          case TlaSetOper.supsetProper => mkOpApp( "", args : _* )
          case TlaSetOper.times => mkOpApp( "", args : _* )
          case TlaSetOper.union => mkOpApp( "", args : _* )

          case _ => "TBD"
        }

      case _ => ""
    }
  }
}

object FullPrinter extends Printer {
  override def apply( p_ex : TlaEx ) : String = ""
}