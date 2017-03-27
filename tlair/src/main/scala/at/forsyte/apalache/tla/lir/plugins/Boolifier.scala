/*
package at.forsyte.apalache.tla.lir.plugins

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.lir.actions._
import at.forsyte.apalache.tla.lir.control._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.temporal._

import at.forsyte.apalache.tla.lir.db._

abstract class BoolifierType

case class BoolT() extends BoolifierType
case class NotBoolT() extends BoolifierType
case class PossibleBoolT() extends BoolifierType


object BoolDB extends SmartHashMapDB[ TlaEx, BoolifierType ]{
  override val name = "TypeDB"

  /** Can be more precise with PossibleBoolT() */
  protected def deduceBoolType( ex: TlaEx ): BoolifierType ={
    ex match {
      case ValEx( v ) => v match {
          case TlaBool(_) =>return BoolT()
          case _ => return NotBoolT()
        }
      case NameEx( n ) => return PossibleBoolT()
      case OperEx( op, args @ _* ) => op match {
        case TlaActionOper.prime => {
          return this.apply( args.head ).get
        }
        case TlaActionOper.stutter => return BoolT()
        case TlaActionOper.nostutter => return BoolT()
        case TlaActionOper.enabled => return BoolT()
        case TlaActionOper.unchanged => return BoolT()
        case TlaActionOper.composition => return PossibleBoolT() /**  NOT SURE */

        case TlaOper.eq => return BoolT()
        case TlaOper.ne => return BoolT()
        case TlaOper.apply => {
          val body = OperatorDB.body( EquivalenceDB.getRaw( args.head ) )
          //body

          return PossibleBoolT()
        }
        case TlaOper.chooseBounded => return PossibleBoolT()
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
        case TlaSetOper.subsetProper => return BoolT()
        case TlaSetOper.supseteq => return BoolT()
        case TlaSetOper.supsetProper => return BoolT()

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

  def evaluate( key : TlaEx ) : Option[ BoolifierType ] = {
    Some( deduceBoolType( key ) )
  }

}


/**
  * Created by jkukovec on 1/10/17.
  */
object Boolifier extends Plugin {
  override val name = "TypeInference"
  override val dependencies: List[ String ] = FirstPass.name :: EquivalencePlugin.name :: Substitutor.name :: Nil


  override protected def translate( ): Unit = {

  }

  override protected def reTranslate( err: PluginError ): Unit = {

  }
}

*/