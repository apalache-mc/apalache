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

  def value( p_val: BigInt     ) : TlaEx = ValEx( TlaInt( p_val )     )
  def value( p_val: BigDecimal ) : TlaEx = ValEx( TlaDecimal( p_val ) )
  def value( p_val: Boolean    ) : TlaEx = ValEx( TlaBool( p_val )    )
  def value( p_val: String     ) : TlaEx = ValEx( TlaStr( p_val )     )

  /** TlaOper */
  def eq( p_lhs: TlaEx
        , p_rhs: TlaEx
        ) : TlaEx = OperEx(TlaOper.eq, p_lhs, p_rhs        )
  def eq( p_lhs: TlaEx
        , p_rhs: BigInt
        ) : TlaEx = OperEx(TlaOper.eq, p_lhs, value(p_rhs) )

  def ne( p_lhs: TlaEx
        , p_rhs: TlaEx
        ) : TlaEx = OperEx(TlaOper.ne, p_lhs, p_rhs        )
  def ne( p_lhs: TlaEx
        , p_rhs: BigInt
        ) : TlaEx = OperEx(TlaOper.ne, p_lhs, value(p_rhs) )

  def apply( p_Op  : TlaEx
           , p_args: TlaEx*
           ) : TlaEx = OperEx(TlaOper.apply, (p_Op +: p_args):_* )

  def choose( p_x: TlaEx
            , p_S: TlaEx
            ) : TlaEx = OperEx(TlaOper.chooseUnbounded, p_x, p_S      )
  def choose( p_x: TlaEx
            , p_S: TlaEx
            , p_p: TlaEx
            ) : TlaEx = OperEx(TlaOper.chooseBounded  , p_x, p_S, p_p )

  def prime( p_name: String ) : TlaEx =
    OperEx( TlaActionOper.prime, name( p_name ) )
  def prime( p_name: NameEx ) : TlaEx =
    OperEx( TlaActionOper.prime, p_name         )

  def prime_eq( p_name: String
              , p_rhs: TlaEx
              ) : TlaEx = eq( prime(p_name), p_rhs )
  def prime_eq( p_name: NameEx
              , p_rhs: TlaEx
              ) : TlaEx = eq( prime(p_name), p_rhs )

  /** TlaBoolOper */
  def and( p_args: TlaEx* ) : TlaEx = OperEx( TlaBoolOper.and, p_args:_* )

  def or( p_args: TlaEx* ) : TlaEx = OperEx( TlaBoolOper.or, p_args:_* )

  def not( p_P: TlaEx ) : TlaEx = OperEx( TlaBoolOper.not, p_P )

  def implies( p_P: TlaEx
             , p_Q: TlaEx
             ) : TlaEx = OperEx( TlaBoolOper.implies, p_P, p_Q )

  def equiv( p_P: TlaEx
           , p_Q: TlaEx
           ) : TlaEx = OperEx( TlaBoolOper.equiv, p_P, p_Q )

  def forall( p_x: TlaEx
            , p_S: TlaEx
            , p_p: TlaEx
            ) : TlaEx = OperEx( TlaBoolOper.forall         , p_x, p_S, p_p )
  def forall( p_x: TlaEx
            , p_p: TlaEx
            ) : TlaEx = OperEx( TlaBoolOper.forallUnbounded, p_x, p_p      )

  def exists( p_x: TlaEx
            , p_S: TlaEx
            , p_p: TlaEx
            ) : TlaEx = OperEx( TlaBoolOper.exists         , p_x, p_S, p_p )
  def exists( p_x: TlaEx
            , p_p: TlaEx
            ) : TlaEx = OperEx( TlaBoolOper.existsUnbounded, p_x, p_p      )

  /** TlaActionOper */
  def stutter( p_A: TlaEx
             , p_e: TlaEx
             ) : TlaEx = OperEx( TlaActionOper.stutter, p_A, p_e )

  def nostutter( p_A: TlaEx
               , p_e: TlaEx
               ) : TlaEx = OperEx( TlaActionOper.nostutter, p_A, p_e )

  def enabled( p_A: TlaEx ) : TlaEx = OperEx( TlaActionOper.enabled, p_A )

  def unchanged( p_v: TlaEx ) : TlaEx = OperEx( TlaActionOper.unchanged, p_v )

  def composition( p_A: TlaEx
                 , p_B: TlaEx
                 ) : TlaEx = OperEx( TlaActionOper.composition, p_A, p_B )

  /** TlaControlOper */
  def caseSplit( p_p1  : TlaEx
               , p_e1  : TlaEx
               , p_args: TlaEx* /** Expected even size */
               ) : TlaEx =
    OperEx( TlaControlOper.caseNoOther, (p_p1 +: p_e1 +: p_args):_* )

  def caseOther( p_e   : TlaEx
               , p_p1  : TlaEx
               , p_e1  : TlaEx
               , p_args: TlaEx* /** Expected even size */
               ) : TlaEx =
    OperEx( TlaControlOper.caseWithOther, (p_e +: p_p1 +: p_e1 +: p_args):_* )

  def ite( p_cond: TlaEx
         , p_then: TlaEx
         , p_else: TlaEx
         ) : TlaEx = OperEx( TlaControlOper.ifThenElse, p_cond, p_then, p_else )

  /** TlaTempOper */
  def AA( p_x: TlaEx
        , p_F: TlaEx
        ) : TlaEx = OperEx( TlaTempOper.AA, p_x, p_F )

  def EE( p_x: TlaEx
        , p_F: TlaEx
        ) : TlaEx = OperEx( TlaTempOper.EE, p_x, p_F )
  
  def box( p_F: TlaEx ) : TlaEx = OperEx( TlaTempOper.box, p_F )

  def diamond( p_F: TlaEx ) : TlaEx = OperEx( TlaTempOper.diamond, p_F )

  def guarantees( p_F: TlaEx
                , p_G: TlaEx
                ) : TlaEx = OperEx( TlaTempOper.guarantees, p_F, p_G )
  
  def leadsTo( p_F: TlaEx
             , p_G: TlaEx
             ) : TlaEx = OperEx( TlaTempOper.leadsTo, p_F, p_G )

  def SF( p_e: TlaEx
        , p_A: TlaEx
        ) : TlaEx = OperEx( TlaTempOper.strongFairness, p_e, p_A )

  def WF( p_e: TlaEx, p_A: TlaEx ) : TlaEx = OperEx( TlaTempOper.weakFairness, p_e, p_A )

  /** TlaArithOper */
  def sum( p_args: TlaEx*  ) : TlaEx = OperEx( TlaArithOper.sum, p_args:_* )

  def plus( p_a: TlaEx
          , p_b: TlaEx
          ) : TlaEx = OperEx( TlaArithOper.plus, p_a       , p_b        )
  def plus( p_a: TlaEx
          , p_b: BigInt
          ) : TlaEx = OperEx( TlaArithOper.plus, p_a       , value(p_b) )
  def plus( p_a: BigInt
          , p_b: TlaEx
          ) : TlaEx = OperEx( TlaArithOper.plus, value(p_a), p_b        )
  def plus( p_a: BigInt
          , p_b: BigInt
          ) : TlaEx = OperEx( TlaArithOper.plus, value(p_a), value(p_b) )

  def minus( p_a: TlaEx
           , p_b: TlaEx
           ) : TlaEx = OperEx( TlaArithOper.minus, p_a       , p_b        )
  def minus( p_a: TlaEx
           , p_b: BigInt
           ) : TlaEx = OperEx( TlaArithOper.minus, p_a       , value(p_b) )
  def minus( p_a: BigInt
           , p_b: TlaEx
           ) : TlaEx = OperEx( TlaArithOper.minus, value(p_a), p_b        )
  def minus( p_a: BigInt
           , p_b: BigInt
           ) : TlaEx = OperEx( TlaArithOper.minus, value(p_a), value(p_b) )

  def uminus( p_a: TlaEx  ) : TlaEx = OperEx( TlaArithOper.uminus, p_a        )
  def uminus( p_a: BigInt ) : TlaEx = OperEx( TlaArithOper.uminus, value(p_a) )

  def prod( p_args: TlaEx*  ) : TlaEx = OperEx( TlaArithOper.prod, p_args:_* )

  def mult( p_a: TlaEx
          , p_b: TlaEx
          ) : TlaEx = OperEx( TlaArithOper.mult, p_a       , p_b        )
  def mult( p_a: TlaEx
          , p_b: BigInt
          ) : TlaEx = OperEx( TlaArithOper.mult, p_a       , value(p_b) )
  def mult( p_a: BigInt
          , p_b: TlaEx
          ) : TlaEx = OperEx( TlaArithOper.mult, value(p_a), p_b        )
  def mult( p_a: BigInt
          , p_b: BigInt
          ) : TlaEx = OperEx( TlaArithOper.mult, value(p_a), value(p_b) )

  def div( p_a: TlaEx
         , p_b: TlaEx
         ) : TlaEx = OperEx( TlaArithOper.div, p_a       , p_b        )
  def div( p_a: TlaEx
         , p_b: BigInt
         ) : TlaEx = OperEx( TlaArithOper.div, p_a       , value(p_b) )
  def div( p_a: BigInt
         , p_b: TlaEx
         ) : TlaEx = OperEx( TlaArithOper.div, value(p_a), p_b        )
  def div( p_a: BigInt
         , p_b: BigInt
         ) : TlaEx = OperEx( TlaArithOper.div, value(p_a), value(p_b) )

  def mod( p_a: TlaEx
         , p_b: TlaEx
         ) : TlaEx = OperEx( TlaArithOper.mod, p_a       , p_b        )
  def mod( p_a: TlaEx
         , p_b: BigInt
         ) : TlaEx = OperEx( TlaArithOper.mod, p_a       , value(p_b) )
  def mod( p_a: BigInt
         , p_b: TlaEx
         ) : TlaEx = OperEx( TlaArithOper.mod, value(p_a), p_b        )
  def mod( p_a: BigInt
         , p_b: BigInt
         ) : TlaEx = OperEx( TlaArithOper.mod, value(p_a), value(p_b) )

  def realDiv( p_a: TlaEx
             , p_b: TlaEx
             ) : TlaEx = OperEx( TlaArithOper.realDiv, p_a       , p_b        )
  def realDiv( p_a: TlaEx
             , p_b: BigInt
             ) : TlaEx = OperEx( TlaArithOper.realDiv, p_a       , value(p_b) )
  def realDiv( p_a: BigInt
             , p_b: TlaEx
             ) : TlaEx = OperEx( TlaArithOper.realDiv, value(p_a), p_b        )
  def realDiv( p_a: BigInt
             , p_b: BigInt
             ) : TlaEx = OperEx( TlaArithOper.realDiv, value(p_a), value(p_b) )

  def exp( p_a: TlaEx
         , p_b: TlaEx
         ) : TlaEx = OperEx( TlaArithOper.exp, p_a       , p_b        )
  def exp( p_a: TlaEx
         , p_b: BigInt
         ) : TlaEx = OperEx( TlaArithOper.exp, p_a       , value(p_b) )
  def exp( p_a: BigInt
         , p_b: TlaEx
         ) : TlaEx = OperEx( TlaArithOper.exp, value(p_a), p_b        )
  def exp( p_a: BigInt
         , p_b: BigInt
         ) : TlaEx = OperEx( TlaArithOper.exp, value(p_a), value(p_b) )

  def dotdot( p_a: TlaEx
            , p_b: TlaEx
            ) : TlaEx = OperEx( TlaArithOper.dotdot, p_a       , p_b        )
  def dotdot( p_a: TlaEx
            , p_b: BigInt
            ) : TlaEx = OperEx( TlaArithOper.dotdot, p_a       , value(p_b) )
  def dotdot( p_a: BigInt
            , p_b: TlaEx
            ) : TlaEx = OperEx( TlaArithOper.dotdot, value(p_a), p_b        )
  def dotdot( p_a: BigInt
            , p_b: BigInt
            ) : TlaEx = OperEx( TlaArithOper.dotdot, value(p_a), value(p_b) )

  def lt( p_a: TlaEx
        , p_b: TlaEx
        ) : TlaEx = OperEx( TlaArithOper.lt, p_a       , p_b        )
  def lt( p_a: TlaEx
        , p_b: BigInt
        ) : TlaEx = OperEx( TlaArithOper.lt, p_a       , value(p_b) )
  def lt( p_a: BigInt
        , p_b: TlaEx
        ) : TlaEx = OperEx( TlaArithOper.lt, value(p_a), p_b        )
  def lt( p_a: BigInt
        , p_b: BigInt
        ) : TlaEx = OperEx( TlaArithOper.lt, value(p_a), value(p_b) )

  def gt( p_a: TlaEx
        , p_b: TlaEx
        ) : TlaEx = OperEx( TlaArithOper.gt, p_a       , p_b        )
  def gt( p_a: TlaEx
        , p_b: BigInt
        ) : TlaEx = OperEx( TlaArithOper.gt, p_a       , value(p_b) )
  def gt( p_a: BigInt
        , p_b: TlaEx
        ) : TlaEx = OperEx( TlaArithOper.gt, value(p_a), p_b        )
  def gt( p_a: BigInt
        , p_b: BigInt
        ) : TlaEx = OperEx( TlaArithOper.gt, value(p_a), value(p_b) )

  def le( p_a: TlaEx
        , p_b: TlaEx
        ) : TlaEx = OperEx( TlaArithOper.le, p_a       , p_b        )
  def le( p_a: TlaEx
        , p_b: BigInt
        ) : TlaEx = OperEx( TlaArithOper.le, p_a       , value(p_b) )
  def le( p_a: BigInt
        , p_b: TlaEx
        ) : TlaEx = OperEx( TlaArithOper.le, value(p_a), p_b        )
  def le( p_a: BigInt
        , p_b: BigInt
        ) : TlaEx = OperEx( TlaArithOper.le, value(p_a), value(p_b) )

  def ge( p_a: TlaEx
        , p_b: TlaEx
        ) : TlaEx = OperEx( TlaArithOper.ge, p_a       , p_b        )
  def ge( p_a: TlaEx
        , p_b: BigInt
        ) : TlaEx = OperEx( TlaArithOper.ge, p_a       , value(p_b) )
  def ge( p_a: BigInt
        , p_b: TlaEx
        ) : TlaEx = OperEx( TlaArithOper.ge, value(p_a), p_b        )
  def ge( p_a: BigInt
        , p_b: BigInt
        ) : TlaEx = OperEx( TlaArithOper.ge, value(p_a), value(p_b) )

  /** TlaFiniteSetOper */
  def card( p_S: TlaEx ) : TlaEx = OperEx( TlaFiniteSetOper.cardinality, p_S )

  def isFin( p_S: TlaEx ) : TlaEx = OperEx( TlaFiniteSetOper.isFiniteSet, p_S )

  /** TlaFunOper */
  def app( p_f   : TlaEx
         , p_args: TlaEx*
         ) : TlaEx = OperEx( TlaFunOper.app, (p_f +: p_args):_* )

  def dom( p_f: TlaEx ) : TlaEx = OperEx( TlaFunOper.domain, p_f )

  def enum( p_k1  : TlaEx
          , p_v1  : TlaEx
          , p_args: TlaEx* /** Expected even size */
          ) : TlaEx = OperEx( TlaFunOper.enum, (p_k1 +: p_v1 +:p_args):_* )

  def except( p_f   : TlaEx
            , p_k1  : TlaEx
            , p_v1  : TlaEx
            , p_args: TlaEx* /** Expected even size */
            ) : TlaEx =
    OperEx( TlaFunOper.except, (p_f +: p_k1 +: p_v1 +: p_args):_* )

  def funDef( p_e   : TlaEx
            , p_x   : TlaEx
            , p_S   : TlaEx
            , p_args: TlaEx* /** Expected even size */
            ) : TlaEx =
    OperEx( TlaFunOper.funDef, (p_e +: p_x +: p_S +: p_args):_* )

  def tuple( p_args: TlaEx* ) : TlaEx = OperEx( TlaFunOper.tuple, p_args:_* )

  /** TlaSeqOper */
  def append( p_s: TlaEx
            , p_e: TlaEx
            ) : TlaEx = OperEx( TlaSeqOper.append, p_s, p_e )

  def concat( p_s1: TlaEx
            , p_s2: TlaEx
            ) : TlaEx = OperEx( TlaSeqOper.concat, p_s1, p_s2 )

  def head( p_s: TlaEx ) : TlaEx = OperEx( TlaSeqOper.head, p_s )

  def tail( p_s: TlaEx ) : TlaEx = OperEx( TlaSeqOper.tail, p_s )

  def len( p_s: TlaEx ) : TlaEx = OperEx( TlaSeqOper.len, p_s )

  /** TlaSetOper */
  def enumSet( p_args: TlaEx* ) : TlaEx =
    OperEx( TlaSetOper.enumSet, p_args:_* )

  def in( p_x: TlaEx
        , p_S: TlaEx
        ) : TlaEx = OperEx( TlaSetOper.in, p_x, p_S )

  def notin( p_x: TlaEx
           , p_S: TlaEx
           ) : TlaEx = OperEx( TlaSetOper.notin, p_x, p_S )

  def cap( p_S1: TlaEx
         , p_S2: TlaEx
         ) : TlaEx = OperEx( TlaSetOper.cap, p_S1, p_S2)
  
  def cup( p_S1: TlaEx
         , p_S2: TlaEx
         ) : TlaEx = OperEx( TlaSetOper.cup, p_S1, p_S2)

  def union( p_args: TlaEx* ) : TlaEx = OperEx( TlaSetOper.union, p_args:_* )

  def filter( p_x: TlaEx
            , p_S: TlaEx
            , p_p: TlaEx
            ) : TlaEx = OperEx( TlaSetOper.filter, p_x, p_S, p_p )

  def map( p_e   : TlaEx
         , p_x   : TlaEx
         , p_S   : TlaEx
         , p_args: TlaEx* /** Expected even size */
         ) : TlaEx = OperEx( TlaSetOper.map, (p_e +: p_x +: p_S +: p_args):_* )
  
  def funSet( p_S: TlaEx
            , p_T: TlaEx
            ) : TlaEx = OperEx( TlaSetOper.funSet, p_S, p_T)

  def recSet( p_args: TlaEx* ) : TlaEx = OperEx( TlaSetOper.recSet, p_args:_* )

  def seqSet( p_S: TlaEx ) : TlaEx = OperEx( TlaSetOper.seqSet, p_S )

  def subset( p_S1: TlaEx
            , p_S2: TlaEx
            ) : TlaEx = OperEx( TlaSetOper.subsetProper, p_S1, p_S2)

  def subseteq( p_S1: TlaEx
              , p_S2: TlaEx
              ) : TlaEx = OperEx( TlaSetOper.subseteq, p_S1, p_S2)

  def supset( p_S1: TlaEx
            , p_S2: TlaEx
            ) : TlaEx = OperEx( TlaSetOper.supsetProper, p_S1, p_S2)

  def supseteq( p_S1: TlaEx
              , p_S2: TlaEx
              ) : TlaEx = OperEx( TlaSetOper.supseteq, p_S1, p_S2)

  def setminus( p_S1: TlaEx
              , p_S2: TlaEx
              ) : TlaEx = OperEx( TlaSetOper.setminus, p_S1, p_S2)

  def times( p_S1: TlaEx
           , p_S2: TlaEx
           ) : TlaEx = OperEx( TlaSetOper.times, p_S1, p_S2)

  def powSet( p_S: TlaEx ) : TlaEx = OperEx( TlaSetOper.powerset, p_S )

  val m_nameMap : Map[String, TlaOper] =
    scala.collection.immutable.Map(
      TlaOper.eq.name              -> TlaOper.eq,
      TlaOper.ne.name              -> TlaOper.ne,
      TlaOper.apply.name           -> TlaOper.apply,
      TlaOper.chooseBounded.name   -> TlaOper.chooseBounded,
      TlaOper.chooseUnbounded.name -> TlaOper.chooseUnbounded,

      TlaBoolOper.and.name             -> TlaBoolOper.and,
      TlaBoolOper.or.name              -> TlaBoolOper.or,
      TlaBoolOper.not.name             -> TlaBoolOper.not,
      TlaBoolOper.implies.name         -> TlaBoolOper.implies,
      TlaBoolOper.equiv.name           -> TlaBoolOper.equiv,
      TlaBoolOper.forall.name          -> TlaBoolOper.forall,
      TlaBoolOper.exists.name          -> TlaBoolOper.exists,
      TlaBoolOper.forallUnbounded.name -> TlaBoolOper.forallUnbounded,
      TlaBoolOper.existsUnbounded.name -> TlaBoolOper.existsUnbounded,

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

  def operByName( p_operName: String
                , p_args    : TlaEx* /** Expected to match operator arity */
                ): TlaEx= OperEx( m_nameMap(p_operName), p_args:_*)

  def operByNameOrNull( p_operName: String
                      , p_args    : TlaEx*
                      ) : TlaEx =
    m_nameMap.get(p_operName).map(
      op =>
        if (op.isCorrectArity(p_args.size))
          OperEx( op, p_args:_* )
        else NullEx
    ).getOrElse(NullEx)
}
