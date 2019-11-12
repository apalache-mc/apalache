package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.predef.TlaBoolSet
import at.forsyte.apalache.tla.lir.values._


/* TODO: LET-IN operator!!! */
/* TODO: the argument names should be self-explanatory, e.g., I cannot see how to use funDef (Igor, 19.11.2017) */

/**
  * A builder for TLA expressions.
  *
  * Contains methods for constructing various types of [[TlaEx]] expressions, guaranteeing
  * correct arity where the arity of the associated [[oper.TlaOper TlaOper]] is fixed.
  *
  * @author jkukovec
  */
object Builder {

  /** Names and values */
  implicit def name( p_name : String ) : NameEx = NameEx( p_name )

  def bigInt( p_val : BigInt ) : ValEx = ValEx( TlaInt( p_val ) )

  def decimal( p_val : BigDecimal ) : ValEx = ValEx( TlaDecimal( p_val ) )

  implicit def int( p_val : Int ) : ValEx = ValEx( TlaInt( p_val ) )

  implicit def bool( p_val : Boolean ) : ValEx = ValEx( TlaBool( p_val ) )

  def str( p_val : String ) : ValEx = ValEx( TlaStr( p_val ) )

  /**
    * The set BOOLEAN.
    *
    * @return the value expression that corresponds to BOOLEAN.
    */
  def booleanSet(): ValEx = ValEx(TlaBoolSet)

  /** Declarations */

  def declOp( p_name : String,
              p_body : TlaEx,
              p_args : FormalParam*
            ) : TlaOperDecl = TlaOperDecl( p_name, p_args.toList, p_body )

  def appDecl( p_decl : TlaOperDecl,
               p_args : TlaEx*
             ) : OperEx = {
    if ( p_args.length == p_decl.formalParams.length )
      OperEx( TlaOper.apply, name( p_decl.name ) +: p_args : _* )
    else
      throw new IllegalArgumentException
  }

  /** TlaOper */
  def eql( p_lhs : TlaEx,
           p_rhs : TlaEx
         ) : OperEx = OperEx( TlaOper.eq, p_lhs, p_rhs )

  def neql( p_lhs : TlaEx,
            p_rhs : TlaEx
          ) : OperEx = OperEx( TlaOper.ne, p_lhs, p_rhs )

  def appOp( p_Op : TlaEx,
             p_args : TlaEx*
           ) : OperEx = OperEx( TlaOper.apply, p_Op +: p_args : _* )

  def choose( p_x : TlaEx,
              p_p : TlaEx
            ) : OperEx = OperEx( TlaOper.chooseUnbounded, p_x, p_p )

  def choose( p_x : TlaEx,
              p_S : TlaEx,
              p_p : TlaEx
            ) : OperEx = OperEx( TlaOper.chooseBounded, p_x, p_S, p_p )

  /**
    * Decorate a TLA+ expression with a label (a TLA+2 feature), e.g.,
    * lab(a, b) :: e decorates e with the label "lab" whose arguments are "a" and "b".
    * @param ex a TLA+ expression to decorate
    * @param name label identifier
    * @param args label arguments (also identifiers)
    * @return OperEx(TlaOper.label, ex, name as NameEx, args as NameEx)
    */
  def label(ex: TlaEx, name: String, args: String*): OperEx = {
    OperEx(TlaOper.label, ex +: ValEx(TlaStr(name)) +: args.map(s => ValEx(TlaStr(s))) :_*)
  }


  /** TlaBoolOper */
  def and( p_args : TlaEx* ) : OperEx = OperEx( TlaBoolOper.and, p_args : _* )

  def or( p_args : TlaEx* ) : OperEx = OperEx( TlaBoolOper.or, p_args : _* )

  def not( p_P : TlaEx ) : OperEx = OperEx( TlaBoolOper.not, p_P )

  def impl( p_P : TlaEx,
            p_Q : TlaEx
          ) : OperEx = OperEx( TlaBoolOper.implies, p_P, p_Q )

  def equiv( p_P : TlaEx,
             p_Q : TlaEx
           ) : OperEx = OperEx( TlaBoolOper.equiv, p_P, p_Q )

  def forall( p_x : TlaEx,
              p_S : TlaEx,
              p_p : TlaEx
            ) : OperEx = OperEx( TlaBoolOper.forall, p_x, p_S, p_p )

  def forall( p_x : TlaEx,
              p_p : TlaEx
            ) : OperEx = OperEx( TlaBoolOper.forallUnbounded, p_x, p_p )

  def exists( p_x : TlaEx,
              p_S : TlaEx,
              p_p : TlaEx
            ) : OperEx = OperEx( TlaBoolOper.exists, p_x, p_S, p_p )

  def exists( p_x : TlaEx,
              p_p : TlaEx
            ) : OperEx = OperEx( TlaBoolOper.existsUnbounded, p_x, p_p )

  /** TlaActionOper */
  def prime( p_name : TlaEx ) : OperEx = OperEx( TlaActionOper.prime, p_name )

  def primeEq( p_name : TlaEx,
               p_rhs : TlaEx
             ) : OperEx = eql( prime( p_name ), p_rhs )

  def stutt( p_A : TlaEx,
             p_e : TlaEx
           ) : OperEx = OperEx( TlaActionOper.stutter, p_A, p_e )

  def nostutt( p_A : TlaEx,
               p_e : TlaEx
             ) : OperEx = OperEx( TlaActionOper.nostutter, p_A, p_e )

  def enabled( p_A : TlaEx ) : OperEx = OperEx( TlaActionOper.enabled, p_A )

  def unchanged( p_v : TlaEx ) : OperEx = OperEx( TlaActionOper.unchanged, p_v )

  /** UNTESTED */
  def unchangedTup( p_args : TlaEx* ) : OperEx = unchanged( tuple( p_args : _* ) )

  def comp( p_A : TlaEx
            , p_B : TlaEx
          ) : OperEx = OperEx( TlaActionOper.composition, p_A, p_B )

  /** TlaControlOper */
  def caseAny( p_arg1 : TlaEx,
               p_arg2 : TlaEx,
               p_args : TlaEx*
             ) : OperEx =
    if ( p_args.size % 2 == 0 )
      caseSplit( p_arg1, p_arg2, p_args : _* )
    else
      caseOther( p_arg1, p_arg2, p_args.head, p_args.tail : _* )

  def caseSplit( p_p1 : TlaEx,
                 p_e1 : TlaEx,
                 p_args : TlaEx* /* Expected even size */
               ) : OperEx = OperEx( TlaControlOper.caseNoOther, p_p1 +: p_e1 +: p_args : _* )

  def caseOther(p_other : TlaEx,
                p_p1 : TlaEx,
                p_e1 : TlaEx,
                p_args : TlaEx* /* Expected even size */
               ) : OperEx =
    OperEx( TlaControlOper.caseWithOther, p_other +: p_p1 +: p_e1 +: p_args : _* )

  def ite( p_cond : TlaEx,
           p_then : TlaEx,
           p_else : TlaEx
         ) : OperEx = OperEx( TlaControlOper.ifThenElse, p_cond, p_then, p_else )

  // [[LetIn]]
  def letIn( p_ex : TlaEx,
             p_defs : TlaOperDecl*
           ) : LetInEx = LetInEx( p_ex, p_defs : _* )

  /** TlaTempOper */
  def AA( p_x : TlaEx,
          p_F : TlaEx
        ) : OperEx = OperEx( TlaTempOper.AA, p_x, p_F )

  def EE( p_x : TlaEx,
          p_F : TlaEx
        ) : OperEx = OperEx( TlaTempOper.EE, p_x, p_F )

  def box( p_F : TlaEx ) : OperEx = OperEx( TlaTempOper.box, p_F )

  def diamond( p_F : TlaEx ) : OperEx = OperEx( TlaTempOper.diamond, p_F )

  def guarantees( p_F : TlaEx,
                  p_G : TlaEx
                ) : OperEx = OperEx( TlaTempOper.guarantees, p_F, p_G )

  def leadsTo( p_F : TlaEx,
               p_G : TlaEx
             ) : OperEx = OperEx( TlaTempOper.leadsTo, p_F, p_G )

  def SF( p_e : TlaEx,
          p_A : TlaEx
        ) : OperEx = OperEx( TlaTempOper.strongFairness, p_e, p_A )

  def WF( p_e : TlaEx,
          p_A : TlaEx
        ) : OperEx = OperEx( TlaTempOper.weakFairness, p_e, p_A )

  /** TlaArithOper */
  def sum( p_args : TlaEx* ) : OperEx = OperEx( TlaArithOper.sum, p_args : _* )

  def plus( p_a : TlaEx,
            p_b : TlaEx
          ) : OperEx = OperEx( TlaArithOper.plus, p_a, p_b )

  def minus( p_a : TlaEx,
             p_b : TlaEx
           ) : OperEx = OperEx( TlaArithOper.minus, p_a, p_b )

  def uminus( p_a : TlaEx ) : OperEx = OperEx( TlaArithOper.uminus, p_a )

  def prod( p_args : TlaEx* ) : OperEx = OperEx( TlaArithOper.prod, p_args : _* )

  def mult( p_a : TlaEx,
            p_b : TlaEx
          ) : OperEx = OperEx( TlaArithOper.mult, p_a, p_b )

  def div( p_a : TlaEx,
           p_b : TlaEx
         ) : OperEx = OperEx( TlaArithOper.div, p_a, p_b )


  def mod( p_a : TlaEx,
           p_b : TlaEx
         ) : OperEx = OperEx( TlaArithOper.mod, p_a, p_b )


  def rDiv( p_a : TlaEx,
            p_b : TlaEx
          ) : OperEx = OperEx( TlaArithOper.realDiv, p_a, p_b )

  def exp( p_a : TlaEx,
           p_b : TlaEx
         ) : OperEx = OperEx( TlaArithOper.exp, p_a, p_b )

  def dotdot( p_a : TlaEx,
              p_b : TlaEx
            ) : OperEx = OperEx( TlaArithOper.dotdot, p_a, p_b )

  def lt( p_a : TlaEx,
          p_b : TlaEx
        ) : OperEx = OperEx( TlaArithOper.lt, p_a, p_b )

  def gt( p_a : TlaEx,
          p_b : TlaEx
        ) : OperEx = OperEx( TlaArithOper.gt, p_a, p_b )

  def le( p_a : TlaEx,
          p_b : TlaEx
        ) : OperEx = OperEx( TlaArithOper.le, p_a, p_b )

  def ge( p_a : TlaEx,
          p_b : TlaEx
        ) : OperEx = OperEx( TlaArithOper.ge, p_a, p_b )

  /** TlaFiniteSetOper */
  def card( p_S : TlaEx ) : OperEx = OperEx( TlaFiniteSetOper.cardinality, p_S )

  def isFin( p_S : TlaEx ) : OperEx = OperEx( TlaFiniteSetOper.isFiniteSet, p_S )

  /** TlaFunOper */
  def appFun( p_f : TlaEx,
              p_e : TlaEx
            ) : OperEx = OperEx( TlaFunOper.app, p_f, p_e )

  def dom( p_f : TlaEx ) : OperEx = OperEx( TlaFunOper.domain, p_f )

  def enumFun( p_k1 : TlaEx,
               p_v1 : TlaEx,
               p_args : TlaEx* /* Expected even size */
             ) : OperEx = OperEx( TlaFunOper.enum, p_k1 +: p_v1 +: p_args : _* )

  def except( p_f : TlaEx,
              p_k1 : TlaEx,
              p_v1 : TlaEx,
              p_args : TlaEx* /* Expected even size */
            ) : OperEx = {
    OperEx( TlaFunOper.except, p_f +: p_k1 +: p_v1 +: p_args : _* )
  }

  def funDef( p_e : TlaEx,
              p_x : TlaEx,
              p_S : TlaEx,
              p_args : TlaEx* /* Expected even size */
            ) : OperEx = OperEx( TlaFunOper.funDef, p_e +: p_x +: p_S +: p_args : _* )

  def tuple( p_args : TlaEx* ) : OperEx = OperEx( TlaFunOper.tuple, p_args : _* )

  /** TlaSeqOper */
  def append( p_s : TlaEx,
              p_e : TlaEx
            ) : OperEx = OperEx( TlaSeqOper.append, p_s, p_e )

  def concat( p_s1 : TlaEx,
              p_s2 : TlaEx
            ) : OperEx = OperEx( TlaSeqOper.concat, p_s1, p_s2 )

  def head( p_s : TlaEx ) : OperEx = OperEx( TlaSeqOper.head, p_s )

  def tail( p_s : TlaEx ) : OperEx = OperEx( TlaSeqOper.tail, p_s )

  def len( p_s : TlaEx ) : OperEx = OperEx( TlaSeqOper.len, p_s )

  /**
    * Get a subsequence of S, that is, SubSeq(S, from, to)
    * @param seq a sequence, e.g., constructed with tla.tuple
    * @param from the first index of the subsequene, greater or equal to 1
    * @param to the last index of the subsequence, not greater than Len(S)
    * @return the expression that corresponds to SubSeq(S, from, to)
    */
  def subseq(seq: TlaEx, from: TlaEx, to: TlaEx): TlaEx =
    OperEx(TlaSeqOper.subseq, seq, from, to)

  /**
    * Get the subsequence of S that consists of the elements matching a predicate.
    * @param seq a sequence
    * @param test a predicate, it should be an action name
    * @return the expression that corresponds to SelectSeq(S, test)
    */
  def selectseq(seq: TlaEx, test: TlaEx): TlaEx =
    OperEx(TlaSeqOper.selectseq, seq, test)

  /** TlaSetOper */
  def enumSet( p_args : TlaEx* ) : OperEx = OperEx( TlaSetOper.enumSet, p_args : _* )

  def emptySet() : OperEx = enumSet()

  def in( p_x : TlaEx,
          p_S : TlaEx
        ) : OperEx = OperEx( TlaSetOper.in, p_x, p_S )

  def notin( p_x : TlaEx,
             p_S : TlaEx
           ) : OperEx = OperEx( TlaSetOper.notin, p_x, p_S )

  def cap( p_S1 : TlaEx,
           p_S2 : TlaEx
         ) : OperEx = OperEx( TlaSetOper.cap, p_S1, p_S2 )

  def cup( p_S1 : TlaEx,
           p_S2 : TlaEx
         ) : OperEx = OperEx( TlaSetOper.cup, p_S1, p_S2 )

  def union( p_S : TlaEx ) : OperEx = OperEx( TlaSetOper.union, p_S )

  def filter( p_x : TlaEx,
              p_S : TlaEx,
              p_p : TlaEx
            ) : OperEx = OperEx( TlaSetOper.filter, p_x, p_S, p_p )

  def map( p_e : TlaEx,
           p_x : TlaEx,
           p_S : TlaEx,
           p_args : TlaEx* /* Expected even size */
         ) : OperEx = OperEx( TlaSetOper.map, p_e +: p_x +: p_S +: p_args : _* )

  def funSet( p_S : TlaEx,
              p_T : TlaEx
            ) : OperEx = OperEx( TlaSetOper.funSet, p_S, p_T )

  def recSet( p_args : TlaEx* /* Expected even size */
            ) : OperEx = OperEx( TlaSetOper.recSet, p_args : _* )

  def seqSet( p_S : TlaEx ) : OperEx = OperEx( TlaSetOper.seqSet, p_S )

  def subset( p_S1 : TlaEx,
              p_S2 : TlaEx
            ) : OperEx = OperEx( TlaSetOper.subsetProper, p_S1, p_S2 )

  def subseteq( p_S1 : TlaEx,
                p_S2 : TlaEx
              ) : OperEx = OperEx( TlaSetOper.subseteq, p_S1, p_S2 )

  def supset( p_S1 : TlaEx,
              p_S2 : TlaEx
            ) : OperEx = OperEx( TlaSetOper.supsetProper, p_S1, p_S2 )

  def supseteq( p_S1 : TlaEx,
                p_S2 : TlaEx
              ) : OperEx = OperEx( TlaSetOper.supseteq, p_S1, p_S2 )

  def setminus( p_S1 : TlaEx,
                p_S2 : TlaEx
              ) : OperEx = OperEx( TlaSetOper.setminus, p_S1, p_S2 )

  def times( p_args : TlaEx* ) : OperEx = OperEx( TlaSetOper.times, p_args : _* )

  def powSet( p_S : TlaEx ) : OperEx = OperEx( TlaSetOper.powerset, p_S )

  // tlc
  def tlcAssert( e: TlaEx, msg: String ): OperEx = OperEx(TlcOper.assert, e, ValEx(TlaStr(msg)))

  def primeInSingleton( p_x : TlaEx,
                        p_y : TlaEx
                      ) : OperEx = in( prime( p_x ), enumSet( p_y ) )

  // bmc
  def withType(expr: TlaEx, typeAnnot: TlaEx): OperEx =
    OperEx(BmcOper.withType, expr, typeAnnot)


  private val m_nameMap : Map[String, TlaOper] =
    scala.collection.immutable.Map(
      TlaOper.eq.name -> TlaOper.eq,
      TlaOper.ne.name -> TlaOper.ne,
      TlaOper.apply.name -> TlaOper.apply,
      TlaOper.chooseBounded.name -> TlaOper.chooseBounded,
      TlaOper.chooseUnbounded.name -> TlaOper.chooseUnbounded,

      TlaBoolOper.and.name -> TlaBoolOper.and,
      TlaBoolOper.or.name -> TlaBoolOper.or,
      TlaBoolOper.not.name -> TlaBoolOper.not,
      TlaBoolOper.implies.name -> TlaBoolOper.implies,
      TlaBoolOper.equiv.name -> TlaBoolOper.equiv,
      TlaBoolOper.forall.name -> TlaBoolOper.forall,
      TlaBoolOper.exists.name -> TlaBoolOper.exists,
      TlaBoolOper.forallUnbounded.name -> TlaBoolOper.forallUnbounded,
      TlaBoolOper.existsUnbounded.name -> TlaBoolOper.existsUnbounded,

      TlaActionOper.prime.name -> TlaActionOper.prime,
      TlaActionOper.stutter.name -> TlaActionOper.stutter,
      TlaActionOper.nostutter.name -> TlaActionOper.nostutter,
      TlaActionOper.enabled.name -> TlaActionOper.enabled,
      TlaActionOper.unchanged.name -> TlaActionOper.unchanged,
      TlaActionOper.composition.name -> TlaActionOper.composition,

      TlaControlOper.caseNoOther.name -> TlaControlOper.caseNoOther,
      TlaControlOper.caseWithOther.name -> TlaControlOper.caseWithOther,
      TlaControlOper.ifThenElse.name -> TlaControlOper.ifThenElse,

      TlaTempOper.AA.name -> TlaTempOper.AA,
      TlaTempOper.box.name -> TlaTempOper.box,
      TlaTempOper.diamond.name -> TlaTempOper.diamond,
      TlaTempOper.EE.name -> TlaTempOper.EE,
      TlaTempOper.guarantees.name -> TlaTempOper.guarantees,
      TlaTempOper.leadsTo.name -> TlaTempOper.leadsTo,
      TlaTempOper.strongFairness.name -> TlaTempOper.strongFairness,
      TlaTempOper.weakFairness.name -> TlaTempOper.weakFairness,

      TlaArithOper.sum.name -> TlaArithOper.sum,
      TlaArithOper.plus.name -> TlaArithOper.plus,
      TlaArithOper.uminus.name -> TlaArithOper.uminus,
      TlaArithOper.minus.name -> TlaArithOper.minus,
      TlaArithOper.prod.name -> TlaArithOper.prod,
      TlaArithOper.mult.name -> TlaArithOper.mult,
      TlaArithOper.div.name -> TlaArithOper.div,
      TlaArithOper.mod.name -> TlaArithOper.mod,
      TlaArithOper.realDiv.name -> TlaArithOper.realDiv,
      TlaArithOper.exp.name -> TlaArithOper.exp,
      TlaArithOper.dotdot.name -> TlaArithOper.dotdot,
      TlaArithOper.lt.name -> TlaArithOper.lt,
      TlaArithOper.gt.name -> TlaArithOper.gt,
      TlaArithOper.le.name -> TlaArithOper.le,
      TlaArithOper.ge.name -> TlaArithOper.ge,

      TlaFiniteSetOper.cardinality.name -> TlaFiniteSetOper.cardinality,
      TlaFiniteSetOper.isFiniteSet.name -> TlaFiniteSetOper.isFiniteSet,

      TlaFunOper.app.name -> TlaFunOper.app,
      TlaFunOper.domain.name -> TlaFunOper.domain,
      TlaFunOper.enum.name -> TlaFunOper.enum,
      TlaFunOper.except.name -> TlaFunOper.except,
      TlaFunOper.funDef.name -> TlaFunOper.funDef,
      TlaFunOper.tuple.name -> TlaFunOper.tuple,

      TlaSeqOper.append.name -> TlaSeqOper.append,
      TlaSeqOper.concat.name -> TlaSeqOper.concat,
      TlaSeqOper.head.name -> TlaSeqOper.head,
      TlaSeqOper.tail.name -> TlaSeqOper.tail,
      TlaSeqOper.len.name -> TlaSeqOper.len,

      TlaSetOper.enumSet.name -> TlaSetOper.enumSet,
      TlaSetOper.in.name -> TlaSetOper.in,
      TlaSetOper.notin.name -> TlaSetOper.notin,
      TlaSetOper.cap.name -> TlaSetOper.cap,
      TlaSetOper.cup.name -> TlaSetOper.cup,
      TlaSetOper.filter.name -> TlaSetOper.filter,
      TlaSetOper.funSet.name -> TlaSetOper.funSet,
      TlaSetOper.map.name -> TlaSetOper.map,
      TlaSetOper.powerset.name -> TlaSetOper.powerset,
      TlaSetOper.recSet.name -> TlaSetOper.recSet,
      TlaSetOper.seqSet.name -> TlaSetOper.seqSet,
      TlaSetOper.setminus.name -> TlaSetOper.setminus,
      TlaSetOper.subseteq.name -> TlaSetOper.subseteq,
      TlaSetOper.subsetProper.name -> TlaSetOper.subsetProper,
      TlaSetOper.supseteq.name -> TlaSetOper.supseteq,
      TlaSetOper.supsetProper.name -> TlaSetOper.supsetProper,
      TlaSetOper.times.name -> TlaSetOper.times,
      TlaSetOper.union.name -> TlaSetOper.union
    )

  def byName( p_operName : String,
              p_args : TlaEx* /* Expected to match operator arity */
            ) : TlaEx = OperEx( m_nameMap( p_operName ), p_args : _* )

  def byNameOrNull( p_operName : String,
                    p_args : TlaEx*
                  ) : TlaEx =
    m_nameMap.get( p_operName ).map(
      op =>
        if ( op.isCorrectArity( p_args.size ) )
          OperEx( op, p_args : _* )
        else NullEx
    ).getOrElse( NullEx )
}
