/*
package at.forsyte.apalache.tla.lir.plugins

import at.forsyte.apalache.tla.lir.db._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions._
import at.forsyte.apalache.tla.lir.control._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.temporal._
import at.forsyte.apalache.tla.lir.values._

abstract class CoarseType {
  def <=( other: CoarseType ): Boolean ={
    ( this, other ) match {
      case ( Bot(), _ ) => true
      case ( P( t1 ), P( t2 ) ) => t1 <= t2
      case ( Fun( s1, s2 ), Fun( t1, t2 ) ) => s1 <= t1 && s2 <= t2
      case ( Rec( ss ), Rec( ts ) ) =>
        ss.size <= ts.size &&
        ss.forall( pa => ts.exists( pa2 => pa._1 == pa2._1 && pa._2 <= pa2._2 ) )

      case _ => false
    }
  }
}


case class Bot() extends CoarseType
case class Any() extends  CoarseType
case class TypeVariable( i : scala.Int ) extends CoarseType

case class Bool() extends CoarseType
case class Str() extends CoarseType
case class Numeric() extends CoarseType
case class Int() extends Numeric
case class Real() extends Numeric

case class P( tau: CoarseType ) extends CoarseType
case class Fun( from: CoarseType, to: CoarseType ) extends CoarseType
case class Rec( pairs: Set[(String, CoarseType)] ) extends CoarseType
case class Tup( taus: CoarseType* ) extends CoarseType

case class Variant( taus: CoarseType* ) extends CoarseType
case class Invalid() extends CoarseType


object CoarseTypeDB extends SmartHashMapDB[ TlaEx, CoarseType ]{
  override val name = "CoarseTypeDB"

  // TODO
  override def evaluate( key : TlaEx ) : Option[ CoarseType ] = {
    None
  }

  protected def deduceBoolType( ex: TlaEx ): CoarseType ={
    ex match {
      case ValEx( v ) => v match {
        case TlaBool(_) =>return Bool()

        case TlaInt(_) => return Int()
        //case TlaReal() => return Real() //TlaReal comments say it's unused
        case TlaDecimal(_) => return Real()
        case s: TlaSet => return P( Bot() ) // TODO: Look into set!
        /** Never use memoization, because of operator application,
          * which might evaluate to different types if non-literal arguments change type
          */
//        case TlaFun( domain ) => return Fun( this.apply( ValEx( domain ) ).get, Bot() )
        case TlaFun( domain ) => return Fun( deduceBoolType( ValEx( domain ) ), Bot() )
        case _ => return Bot()
      }
        /** INCLUDE OPERATOR/VAR EXPANSION */
      case NameEx( n ) => return Bot()
      case OperEx( op, args @ _* ) => op match {
        case TlaActionOper.prime => {
          /**
            * Unless it appears in a reassignment, prime has the same type as the unprimed
            */
          return deduceBoolType( args.head )
        }
        case TlaActionOper.stutter => return Bool()
        case TlaActionOper.nostutter => return Bool()
        case TlaActionOper.enabled => return Bool()
        case TlaActionOper.unchanged => return Bool()
        case TlaActionOper.composition => return Invalid() /** TODO: Figure out actual type */

        case TlaOper.eq | TlaOper.ne => {
          val leftT = deduceBoolType( args.head )
          val rightT = deduceBoolType( args.tail.head )

          /**
            * TODO: Memorize types for named vars
            */

          if ( leftT <= rightT || rightT <= leftT ) return Bool()
          else return Invalid()
        }

        case TlaOper.apply => {
          /**
            * TODO: get body from DB
            */
          val body = OperatorDB.body( EquivalenceDB.getRaw( args.head ) )
          body

          return Invalid()
        }
        case TlaOper.chooseBounded => {
          val variable = args.head
          val S = args.tail.head
          val predicate = args.tail.tail.head
        }
        case TlaOper.chooseUnbounded => return PossibleBoolT()

        case TlaArithOper.lt => return BoolT()
        case TlaArithOper.gt => return BoolT()
        case TlaArithOper.le => return BoolT()
        case TlaArithOper.ge => return BoolT()

        case TlaFunOper.app => return PossibleBoolT()

        case TlaSeqOper.head => return PossibleBoolT()

        case TlaSetOper.in => return BoolT()
        case TlaSetOper.notin => return BoolT()
        case TlaSetOper.subseteq => return BoolT()
        case TlaSetOper.subset => return BoolT()
        case TlaSetOper.supseteq => return BoolT()
        case TlaSetOper.supset => return BoolT()

        case oper if
        oper.isInstanceOf[TlaBoolOper] ||
          oper.isInstanceOf[TlaTempOper]
        => return BoolT()

        /** Can be more precise, check all for bool-ness */
        case oper if oper.isInstanceOf[TlaControlOper] => PossibleBoolT()

        case _ => NotBoolT()
      }
    }
  }


}



/**
  * Created by jkukovec on 1/10/17.
  */
object TypeInference extends Plugin{
  override val name = "TypeInference"
  override val dependencies: List[ String ] = FirstPass.name :: EquivalencePlugin.name :: Nil


  override protected def translate(): Unit = {

  }

  override protected def reTranslate( err: PluginError ): Unit = {

  }
}

object CoarseTypeInference extends Plugin{
  override val name = "CoarseTypeInference"
  override val dependencies: List[ String ] = FirstPass.name :: EquivalencePlugin.name :: Nil


  override protected def translate(): Unit = {

  }

  override protected def reTranslate( err: PluginError ): Unit = {

  }
}
*/
