package at.forsyte.apalache.tla.lir.types

import at.forsyte.apalache.tla.lir.db._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._


import scala.collection.immutable.Set

/**
  * Created by jkukovec on 2/24/17.
  */

abstract class GroundSetElement
case class GroundBool( v: Boolean ) extends GroundSetElement
case class GroundInt( v: scala.Int ) extends GroundSetElement
case class GroundNEString( v: String ) extends GroundSetElement{
  require( v.length != 0 )
}
case class GroundConst( v: String ) extends GroundSetElement

abstract class TLAType{
  def <=( other: TLAType ) : Boolean = {
    if( this == other ) true
    ( this, other ) match {
      case ( FinSet( tau, v1 ), FinSet( tau2, v2 ) ) => tau == tau2 && v1.subsetOf( v2 )
      case ( NilSet(), FinSet( tau, v ) | Ints() ) => true
      case _ => false
    }
  }
}

case class Bool() extends TLAType
case class Int() extends TLAType
case class Str() extends TLAType
case class Ints() extends TLAType
case class NilSet() extends TLAType
case class NilSeq() extends TLAType

case class FinSet( tau: TLAType, V: Set[GroundSetElement] ) extends TLAType
case class FinSeq( tau: TLAType, V: Set[GroundSetElement] ) extends TLAType
case class nTuple( n : Int, tau: TLAType) extends TLAType
case class Record( fields: ( String, TLAType )* ) extends TLAType{
  require( fields.forall( pa => pa._1.length != 0 ) )
}
case class Fun( tau1: TLAType, tau2: TLAType ) extends TLAType
case class Union( tau1: TLAType, tau2: TLAType ) extends TLAType
case class Prod( tau1: TLAType, tau2: TLAType ) extends TLAType

case class TypeFail() extends TLAType




object TLATypeDB extends SmartHashMapDB[ TlaEx, TLAType ]{
  override val name = "TLATypeDB"

  implicit def makeTLATypeOption( t: TLAType ) : Option[TLAType] = {
    t match {
      case TypeFail() => None
      case tt => Some( tt )
    }
  }

  implicit def extract( tOpt: Option[ TLAType ] ): TLAType = {
    tOpt.getOrElse( TypeFail() )
  }

  override def evaluate( key: TlaEx ): Option[ TLAType ] = {
    Option( typeInference( key ) ) /** avoid implicit conversion, TypeFail preserves information */
  }

  def typeInference( ex: TlaEx ): TLAType = {
    ex match{

      /** LOGIC */
      case ValEx( v: TlaBool ) => return Bool()
      case OperEx( TlaBoolOper.or
                 | TlaBoolOper.and
                 | TlaBoolOper.implies
                 | TlaBoolOper.equiv,
                e1, e2 ) =>
        if ( TLATypeDB( e1 ).contains( Bool() )
          && TLATypeDB( e2 ).contains( Bool() ) ) {
           return Bool()
        }
      case OperEx( TlaBoolOper.not, e) if TLATypeDB( e ).contains( Bool() ) => return Bool()

      case OperEx( TlaBoolOper.forall | TlaBoolOper.exists | TlaOper.chooseBounded, x , set , p ) => {
        val tauX : TLAType = TLATypeDB( x )
        val tauS : TLAType = TLATypeDB( set )
        val tauP : TLAType = TLATypeDB( p )
        if( tauP == Bool() ){
         tauS match{
           case FinSet( `tauX`, _ ) => return Bool()
           case _ => return TypeFail()
         }
        }
      }

      case OperEx( TlaOper.eq | TlaOper.ne, _ , _ ) => return Bool()

      /** SETS */
      case OperEx( TlaSetOper.in | TlaSetOper.notin, _, _ ) => return Bool()

      case OperEx( TlaSetOper.union, s1, s2 ) => {
        val tau1 : TLAType = TLATypeDB( s1 )
        val tau2 : TLAType = TLATypeDB( s2 )

        ( tau1, tau2 ) match{
          case ( FinSet( t1, v1 ), FinSet( t2, v2 ) ) =>
            return FinSet( if( t1 <= t2  ) t2 else if( t2 <= t1 ) t1 else Union( t1, t2 ), v1.union( v2 ) )
          case _ => return TypeFail()
        }

      }

      case OperEx( TlaSetOper.cup, s1, s2 ) => {
        val tau1 : TLAType = TLATypeDB( s1 )
        val tau2 : TLAType = TLATypeDB( s2 )

        ( tau1, tau2 ) match{
          case ( FinSet( t1, v1 ), FinSet( t2, v2 ) ) if t1 == t2 => return FinSet( t1, v1.intersect( v2 ) )
          case _ => return TypeFail()
        }

      }

      case OperEx( TlaSetOper.filter , x , set , p ) => {
        val tauX : TLAType = TLATypeDB( x )
        val tauS : TLAType = TLATypeDB( set )
        val tauP : TLAType = TLATypeDB( p )
        if( tauP == Bool() ){
          tauS match{
            case FinSet( `tauX`, v ) => return FinSet( tauX, v )
            case _ => return TypeFail()
          }
        }
      }

      case OperEx( TlaSetOper.map , expr , x , set ) => {
        /** TODO, figure out how to get expr(V) */
      }

      case OperEx( TlaSetOper.powerset, set ) => {
        /** TODO, figure out how to get powerset type */
      }

      /** FUNCTIONS */
      case OperEx( TlaFunOper.app, f, e ) => {
        val tauF : TLAType = TLATypeDB( f )
        val tauE : TLAType = TLATypeDB( e )
        tauF match {
          case Fun( `tauE`, tau2 ) => return tau2
          case _ => return TypeFail()
        }
      }

      case OperEx( TlaFunOper.domain, f ) => {
        /** TODO, just take tau1? */
      }

      case


      /** DEFAULT */
      case _ => return TypeFail()
    }
    /** POST-MATCH IF/ELSE */
    return TypeFail()
  }
}

package object types {


}
