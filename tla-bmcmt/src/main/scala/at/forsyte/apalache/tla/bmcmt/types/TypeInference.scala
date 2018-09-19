package at.forsyte.apalache.tla.bmcmt.types

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}

import scalaz._
import Scalaz._

object CounterStates {
  type CounterType = Int
  type CounterState[T] = State[CounterType, T]

  def inc( ) : CounterState[CounterType] = State[CounterType, CounterType] {
    s => (s + 1, s)
  }
}

object Signatures {

  import CounterStates._

  sealed case class Signature( typeParams : List[TypeParam], args : List[CellT], res : CellT ) {

    override def toString : String = {
      val ts = typeParams map {
        _.signature
      } mkString ", "
      val as = args map {
        _.signature
      } mkString s" ${UTFPrinter.m_times} "
      val prefix = if ( typeParams.isEmpty ) "" else s"${UTFPrinter.m_forall} ${ts} . "
      s"${prefix}${as} ${UTFPrinter.m_rarrow} ${res.signature}"
    }
  }

  private def typeParam( exId : UID, id : Int ) : TypeParam = TypeParam( s"${exId.id}_${id}" )

  def get( op : OperEx ) : Signature = getFresh( op ).run( 0 )._2

  def getFresh( op : OperEx ) : CounterState[Signature] = inc() map { i =>
    val exId = op.ID
    val T = TypeParam( s"c${i}" )

    def ts( n : Int ) : List[TypeParam] = List.range( 1, n + 1 ) map { j =>
      TypeParam( s"c${i}_${j}" )
    }

    val ts2 = ts( 2 )

    val ret = op.oper match {
      // Logic
      /** TODO: Introduce AnyArity and/or */
      case TlaBoolOper.and | TlaBoolOper.or | TlaBoolOper.implies | TlaBoolOper.equiv =>
        Signature( List.empty, List.fill( 2 )( BoolT() ), BoolT() )
      case TlaBoolOper.not =>
        Signature( List.empty, List( BoolT() ), BoolT() )
      case TlaBoolOper.exists | TlaBoolOper.forall =>
        Signature( List( T ), List( T, FinSetT( T ), BoolT() ), BoolT() )
      case TlaOper.chooseBounded =>
        Signature( List( T ), List( T, FinSetT( T ), BoolT() ), OptT( T ) )
      case TlaOper.chooseIdiom =>
        Signature( List( T ), List( FinSetT( T ) ), OptT( T ) )

      // Sets
      case TlaOper.eq | TlaOper.ne | TlaSetOper.in | TlaSetOper.notin | TlaSetOper.subseteq =>
        Signature( ts2, ts2, BoolT() )
      case TlaSetOper.cap | TlaSetOper.cup | TlaSetOper.setminus =>
        Signature( List( T ), List.fill( 2 )( FinSetT( T ) ), FinSetT( T ) )
      case TlaSetOper.enumSet =>
        Signature( List( T ), List.fill( op.args.size )( T ), FinSetT( T ) )
      case TlaSetOper.filter =>
        Signature( List( T ), List( T, FinSetT( T ), BoolT() ), FinSetT( T ) )
      case TlaSetOper.map =>
        val List( t1, t2 ) = ts2
        Signature( ts2, List( t1, t2, FinSetT( t2 ) ), FinSetT( t1 ) )

      // Actions
      case TlaActionOper.prime =>
        val List( t1, t2 ) = ts2
        Signature( ts2, List( t1 ), t2 )

      case _ => Signature( List.empty, List.empty, UnknownT() )
    }
    assert( op.oper.isCorrectArity( ret.args.size ) )
    ret
  }

}

object TypeInference {

  import CounterStates._

  sealed case class isType( v1 : CellT, v2 : CellT )

  def smtVar( id : UID ) : TypeParam = TypeParam( s"b_${id.id}" )

  def smtVar( ex : TlaEx ) : TypeParam = smtVar( ex.ID )

  private def thetaInternal( tlaEx : TlaEx ) : CounterState[List[isType]] = tlaEx match {
    case ex@OperEx( TlaActionOper.prime, NameEx( n ) ) => // if we see x' the smt var for the current expression must be consistent with the type of x' overall
      List( isType( smtVar( ex ), TypeParam( s"${n}'" ) ) ).point[CounterState]
    case ex : OperEx => for {
      sig <- Signatures getFresh ex
      bl = smtVar( ex )
      bls = ex.args map smtVar
      subThetas <- ex.args.toList.traverseS( thetaInternal ).map {
        _.flatten
      }
    } yield isType( bl, sig.res ) +: ( bls.zip( sig.args ) map { case (a, b) => isType( a, b ) } ) ++: subThetas

    case _ => List.empty[isType].point[CounterState]
  }

  def theta( tlaEx : TlaEx ) : List[isType] = thetaInternal( tlaEx ).run( 0 )._2

}
