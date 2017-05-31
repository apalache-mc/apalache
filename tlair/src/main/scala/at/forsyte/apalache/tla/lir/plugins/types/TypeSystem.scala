package at.forsyte.apalache.tla.lir.plugins.types


abstract class Type{
  def <=( other : Type ): Boolean =
    /** reflexive */
    if( this == other )
      return true
    else
      (this, other) match {
        /** the empty set is a subtype of all set types */
        case ( FinSet( tau, SetCell()  ), taus : SetType ) => true

        /** finite sets are subtypes if the types and the sets match */
        case ( FinSet( tau1, v1 ),FinSet( tau2, v2 ) ) => tau1 <= tau2 && v1 <= v2

        /** Records are preserved under field order shuffle and records with more fields are subtypes of those with fewer */
        case ( Rec( fields1 ), Rec( fields2 ) ) => fields2.subsetOf(fields1)

        /** Function subtyping is covariant wrt codomains and contravariant wrt domains */
        case ( Fun( taus1, tau1 ), Fun( taus2, tau2 ) ) => taus2 <= taus1 && tau1 <= tau2

        /** Sum types */
        case ( s1: Sum, s2: Sum ) => {
          val n1 = s1.normalized()
          val n2 = s2.normalized()
          n1.taus.forall( n2.taus.contains(_) ) // Move to sets for O( log n ) contains instead of O(n) ?
        }
        case ( tau, s: Sum ) => s.normalized().taus.contains(tau)



        //        case ( FinSet( taus1, _ ), PowSet(taus2) ) => taus1 == taus2
//        case ( FinSet( Fun(a1,b1), _ ), FunSet(a2,b2)) => (a1,b1) == (a2,b2)
//        case ( FinSet( _, SetCell() ), taus : SetType ) => true
        case _ => false
      }

}

abstract class SetType extends Type{
  def elementType : Type
}

case class TBool( ) extends Type
case class TInt( ) extends Type
case class TString( ) extends Type

case class Fun( taus: SetType, tau: Type ) extends Type

case class Sum( taus: Type* ) extends Type{
  /** We want sums in a way that normalizes to a bracket-less form, due to associativity */
  def isNormal() : Boolean = taus.forall( !_.isInstanceOf[Sum] )

  def normalized() : Sum = {
    def mkseq( tau: Type ): Seq[ Type ] = {
      tau match {
        case sum: Sum => sum.taus
        case nosum => Seq( nosum )
      }
    }
    if( isNormal() ) {
      this
    }
    else {
      val newargs = for ( tau <- taus; x <- mkseq( tau ) ) yield x
      Sum( newargs:_* )
    }
  }
}

case class TypeVar() extends Type

case class FinSet( tau: Type, v: SetCell ) extends SetType{
  override def elementType: Type = tau
}
//case class FunSet( taus: SetType, tau: Type ) extends SetType{
//  override def elementType: Type = Fun( taus, tau )
//}
//case class PowSet( taus : SetType ) extends  SetType{
//  override def elementType: Type = taus
//}

case class FinSeq( tau : Type, v : SetCell ) extends Type

case class Rec( fields: Set[(String, Type)] ) extends Type

case class Tuple( taus: Type* ) extends Type



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
