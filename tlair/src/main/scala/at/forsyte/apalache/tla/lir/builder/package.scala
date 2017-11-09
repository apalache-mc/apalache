package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir.control._
import at.forsyte.apalache.tla.lir.temporal._

/**
  * A builder for TLA expressions
  *
  * @author jkukovec
  */

package object Builder {

  /** Names and values*/
  def name( p_name: String ) : TlaEx = NameEx( p_name )

  def value( p_val: BigInt     ) : TlaEx = ValEx( TlaInt( p_val )                  )
  def value( p_val: BigDecimal ) : TlaEx = ValEx( TlaDecimal( p_val )              )
  def value( p_val: Boolean    ) : TlaEx = ValEx( if (p_val) TlaTrue else TlaFalse )
  def value( p_val: String     ) : TlaEx = ValEx( TlaStr( p_val )                  )

  /** TlaOper */
  def eq( p_lhs: TlaEx, p_rhs: TlaEx  ) : TlaEx = OperEx(TlaOper.eq, p_lhs, p_rhs        )
  def eq( p_lhs: TlaEx, p_rhs: BigInt ) : TlaEx = OperEx(TlaOper.eq, p_lhs, value(p_rhs) )

  def ne( p_lhs: TlaEx, p_rhs: TlaEx  ) : TlaEx = OperEx(TlaOper.ne, p_lhs, p_rhs        )
  def ne( p_lhs: TlaEx, p_rhs: BigInt ) : TlaEx = OperEx(TlaOper.ne, p_lhs, value(p_rhs) )

  def apply( p_args: TlaEx* )  : TlaEx = OperEx(TlaOper.apply, p_args:_* )

  def choose( p_x: TlaEx, p_S: TlaEx             ) : TlaEx = OperEx(TlaOper.chooseUnbounded, p_x, p_S      )
  def choose( p_x: TlaEx, p_S: TlaEx, p_p: TlaEx ) : TlaEx = OperEx(TlaOper.chooseBounded  , p_x, p_S, p_p )

  def prime( p_name: String ) : TlaEx = OperEx( TlaActionOper.prime, name( p_name ) )
  def prime( p_name: NameEx ) : TlaEx = OperEx( TlaActionOper.prime, p_name         )

  def prime_eq( p_name: String, p_rhs: TlaEx ) : TlaEx = eq( prime(p_name), p_rhs )
  def prime_eq( p_name: NameEx, p_rhs: TlaEx ) : TlaEx = eq( prime(p_name), p_rhs )

  /** TlaActionOper */
  def stutter( p_A: TlaEx  , p_e: TlaEx ) : TlaEx = OperEx( TlaActionOper.stutter  , p_A, p_e )
  def nostutter( p_A: TlaEx, p_e: TlaEx ) : TlaEx = OperEx( TlaActionOper.nostutter, p_A, p_e )

  def enabled( p_A: TlaEx ) : TlaEx = OperEx( TlaActionOper.enabled, p_A )

  def unchanged( p_v: TlaEx ) : TlaEx = OperEx( TlaActionOper.unchanged, p_v )

  def composition( p_A: TlaEx, p_B: TlaEx ) : TlaEx = OperEx( TlaActionOper.composition, p_A, p_B )

  /** TlaControlOper */
  def caseSplit( p_args: TlaEx* ) : TlaEx = OperEx( TlaControlOper.caseNoOther, p_args:_* ) // throws on bad arity

  def caseOther( p_args: TlaEx* ) : TlaEx = OperEx( TlaControlOper.caseWithOther, p_args:_* ) // throws on bad arity

  def ite( p_cond: TlaEx, p_then: TlaEx, p_else: TlaEx) : TlaEx = OperEx( TlaControlOper.ifThenElse, p_cond, p_then, p_else )

  /** TlaTempOper */
  def AA( p_x: TlaEx, p_F: TlaEx ) : TlaEx = OperEx( TlaTempOper.AA, p_x, p_F )

  def EE( p_x: TlaEx, p_F: TlaEx ) : TlaEx = OperEx( TlaTempOper.EE, p_x, p_F )
  
  def box( p_F: TlaEx ) : TlaEx = OperEx( TlaTempOper.box, p_F )

  def diamond( p_F: TlaEx ) : TlaEx = OperEx( TlaTempOper.diamond, p_F )

  def guarantees( p_F: TlaEx, p_G: TlaEx ) : TlaEx = OperEx( TlaTempOper.guarantees, p_F, p_G )
  
  def leadsTo( p_F: TlaEx, p_G: TlaEx ) : TlaEx = OperEx( TlaTempOper.leadsTo, p_F, p_G )

  def SF( p_e: TlaEx, p_A: TlaEx ) : TlaEx = OperEx( TlaTempOper.strongFairness, p_e, p_A )

  def WF( p_e: TlaEx, p_A: TlaEx ) : TlaEx = OperEx( TlaTempOper.weakFairness, p_e, p_A )

  /** TlaArithOper */
  def sum( p_args: TlaEx*  ) : TlaEx = OperEx( TlaArithOper.sum, p_args:_*            )
  def sum( p_args: BigInt* )(implicit dummy: DummyImplicit) : TlaEx =
    OperEx( TlaArithOper.sum, p_args.map(value):_* )

  def plus( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.plus, p_a       , p_b        )
  def plus( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.plus, p_a       , value(p_b) )
  def plus( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.plus, value(p_a), p_b        )
  def plus( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.plus, value(p_a), value(p_b) )

  def minus( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.minus, p_a       , p_b        )
  def minus( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.minus, p_a       , value(p_b) )
  def minus( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.minus, value(p_a), p_b        )
  def minus( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.minus, value(p_a), value(p_b) )

  def uminus( p_a: TlaEx  ) : TlaEx = OperEx( TlaArithOper.uminus, p_a        )
  def uminus( p_a: BigInt ) : TlaEx = OperEx( TlaArithOper.uminus, value(p_a) )

  def prod( p_args: TlaEx*  ) : TlaEx = OperEx( TlaArithOper.prod, p_args:_*            )
  def prod( p_args: BigInt* )(implicit dummy: DummyImplicit) : TlaEx =
    OperEx( TlaArithOper.prod, p_args.map(value):_* )

  def mult( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.mult, p_a       , p_b        )
  def mult( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.mult, p_a       , value(p_b) )
  def mult( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.mult, value(p_a), p_b        )
  def mult( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.mult, value(p_a), value(p_b) )

  def div( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.div, p_a       , p_b        )
  def div( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.div, p_a       , value(p_b) )
  def div( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.div, value(p_a), p_b        )
  def div( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.div, value(p_a), value(p_b) )

  def mod( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.mod, p_a       , p_b        )
  def mod( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.mod, p_a       , value(p_b) )
  def mod( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.mod, value(p_a), p_b        )
  def mod( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.mod, value(p_a), value(p_b) )

  def realDiv( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.realDiv, p_a       , p_b        )
  def realDiv( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.realDiv, p_a       , value(p_b) )
  def realDiv( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.realDiv, value(p_a), p_b        )
  def realDiv( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.realDiv, value(p_a), value(p_b) )

  def exp( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.exp, p_a       , p_b        )
  def exp( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.exp, p_a       , value(p_b) )
  def exp( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.exp, value(p_a), p_b        )
  def exp( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.exp, value(p_a), value(p_b) )

  def dotdot( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.dotdot, p_a       , p_b        )
  def dotdot( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.dotdot, p_a       , value(p_b) )
  def dotdot( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.dotdot, value(p_a), p_b        )
  def dotdot( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.dotdot, value(p_a), value(p_b) )

  def lt( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.lt, p_a       , p_b        )
  def lt( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.lt, p_a       , value(p_b) )
  def lt( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.lt, value(p_a), p_b        )
  def lt( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.lt, value(p_a), value(p_b) )

  def gt( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.gt, p_a       , p_b        )
  def gt( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.gt, p_a       , value(p_b) )
  def gt( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.gt, value(p_a), p_b        )
  def gt( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.gt, value(p_a), value(p_b) )

  def le( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.le, p_a       , p_b        )
  def le( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.le, p_a       , value(p_b) )
  def le( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.le, value(p_a), p_b        )
  def le( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.le, value(p_a), value(p_b) )

  def ge( p_a: TlaEx , p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.ge, p_a       , p_b        )
  def ge( p_a: TlaEx , p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.ge, p_a       , value(p_b) )
  def ge( p_a: BigInt, p_b: TlaEx  ) : TlaEx = OperEx( TlaArithOper.ge, value(p_a), p_b        )
  def ge( p_a: BigInt, p_b: BigInt ) : TlaEx = OperEx( TlaArithOper.ge, value(p_a), value(p_b) )

  /** TlaFiniteSetOper */
    /* TODO */
//  TlaFiniteSetOper.cardinality.name -> TlaFiniteSetOper.cardinality,
//  TlaFiniteSetOper.isFiniteSet.name -> TlaFiniteSetOper.isFiniteSet,

  val m_nameMap : Map[String, TlaOper] =
    scala.collection.immutable.Map(
      TlaOper.eq.name              -> TlaOper.eq,
      TlaOper.ne.name              -> TlaOper.ne,
      TlaOper.apply.name           -> TlaOper.apply,
      TlaOper.chooseBounded.name   -> TlaOper.chooseBounded,
      TlaOper.chooseUnbounded.name -> TlaOper.chooseUnbounded,

      TlaActionOper.prime.name       -> TlaActionOper.prime,
      TlaActionOper.stutter.name     -> TlaActionOper.stutter,
      TlaActionOper.nostutter.name   -> TlaActionOper.nostutter,
      TlaActionOper.enabled.name     -> TlaActionOper.enabled,
      TlaActionOper.unchanged.name   -> TlaActionOper.unchanged,
      TlaActionOper.composition.name -> TlaActionOper.composition,

      TlaControlOper.caseNoOther.name   -> TlaControlOper.caseNoOther,
      TlaControlOper.caseWithOther.name -> TlaControlOper.caseWithOther,
      TlaControlOper.ifThenElse.name    -> TlaControlOper.ifThenElse,

      TlaTempOper.AA.name             -> TlaTempOper.AA,
      TlaTempOper.box.name            -> TlaTempOper.box,
      TlaTempOper.diamond.name        -> TlaTempOper.diamond,
      TlaTempOper.EE.name             -> TlaTempOper.EE,
      TlaTempOper.guarantees.name     -> TlaTempOper.guarantees,
      TlaTempOper.leadsTo.name        -> TlaTempOper.leadsTo,
      TlaTempOper.strongFairness.name -> TlaTempOper.strongFairness,
      TlaTempOper.weakFairness.name   -> TlaTempOper.weakFairness,

      TlaArithOper.sum.name     -> TlaArithOper.sum,
      TlaArithOper.plus.name    -> TlaArithOper.plus,
      TlaArithOper.uminus.name  -> TlaArithOper.uminus,
      TlaArithOper.minus.name   -> TlaArithOper.minus,
      TlaArithOper.prod.name    -> TlaArithOper.prod,
      TlaArithOper.mult.name    -> TlaArithOper.mult,
      TlaArithOper.div.name     -> TlaArithOper.div,
      TlaArithOper.mod.name     -> TlaArithOper.mod,
      TlaArithOper.realDiv.name -> TlaArithOper.realDiv,
      TlaArithOper.exp.name     -> TlaArithOper.exp,
      TlaArithOper.dotdot.name  -> TlaArithOper.dotdot,
      TlaArithOper.lt.name      -> TlaArithOper.lt,
      TlaArithOper.gt.name      -> TlaArithOper.gt,
      TlaArithOper.le.name      -> TlaArithOper.le,
      TlaArithOper.ge.name      -> TlaArithOper.ge,

      TlaFiniteSetOper.cardinality.name -> TlaFiniteSetOper.cardinality,
      TlaFiniteSetOper.isFiniteSet.name -> TlaFiniteSetOper.isFiniteSet,

      TlaFunOper.app.name    -> TlaFunOper.app,
      TlaFunOper.domain.name -> TlaFunOper.domain ,
      TlaFunOper.enum.name   -> TlaFunOper.enum ,
      TlaFunOper.except.name -> TlaFunOper.except ,
      TlaFunOper.funDef.name -> TlaFunOper.funDef ,
      TlaFunOper.tuple.name  -> TlaFunOper.tuple,

      TlaSeqOper.append.name -> TlaSeqOper.append,
      TlaSeqOper.concat.name -> TlaSeqOper.concat,
      TlaSeqOper.head.name   -> TlaSeqOper.head,
      TlaSeqOper.tail.name   -> TlaSeqOper.tail,
      TlaSeqOper.len.name    -> TlaSeqOper.len,

      TlaSetOper.enumSet.name      -> TlaSetOper.enumSet,
      TlaSetOper.in.name           -> TlaSetOper.in,
      TlaSetOper.notin.name        -> TlaSetOper.notin,
      TlaSetOper.cap.name          -> TlaSetOper.cap,
      TlaSetOper.cup.name          -> TlaSetOper.cup,
      TlaSetOper.filter.name       -> TlaSetOper.filter,
      TlaSetOper.funSet.name       -> TlaSetOper.funSet,
      TlaSetOper.map.name          -> TlaSetOper.map,
      TlaSetOper.powerset.name     -> TlaSetOper.powerset,
      TlaSetOper.recSet.name       -> TlaSetOper.recSet,
      TlaSetOper.seqSet.name       -> TlaSetOper.seqSet,
      TlaSetOper.setminus.name     -> TlaSetOper.setminus,
      TlaSetOper.subseteq.name     -> TlaSetOper.subseteq,
      TlaSetOper.subsetProper.name -> TlaSetOper.subsetProper,
      TlaSetOper.supseteq.name     -> TlaSetOper.supseteq,
      TlaSetOper.supsetProper.name -> TlaSetOper.supsetProper,
      TlaSetOper.times.name        -> TlaSetOper.times,
      TlaSetOper.union.name        -> TlaSetOper.union
  )

  def oper(p_operName: String, p_args: TlaEx* ) : TlaEx = {
    m_nameMap.get(p_operName).map(
      op => if (op.isCorrectArity(p_args.size)) OperEx( op, p_args:_* ) else NullEx
    ).getOrElse(NullEx)
  }
}
