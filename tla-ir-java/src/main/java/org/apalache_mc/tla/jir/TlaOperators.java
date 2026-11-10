package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.oper.*;

/**
 * Operator constants for inspecting {@code OperEx} values.
 *
 * <p>Compare an expression's {@code oper()} value to these constants by identity. For example,
 * {@code expression.oper() == TlaOperators.PLUS} identifies integer addition.</p>
 */
public final class TlaOperators {
  private TlaOperators() {}

  /** The Apalache!:= IR operator. */
  public static final TlaOper ASSIGN = ApalacheOper.assign$.MODULE$;

  /** The Apalache!Gen IR operator. */
  public static final TlaOper GEN = ApalacheOper.gen$.MODULE$;

  /** The Apalache!Skolem IR operator. */
  public static final TlaOper SKOLEM = ApalacheOper.skolem$.MODULE$;

  /** The Apalache!Guess IR operator. */
  public static final TlaOper GUESS = ApalacheOper.guess$.MODULE$;

  /** The Apalache!Expand IR operator. */
  public static final TlaOper EXPAND = ApalacheOper.expand$.MODULE$;

  /** The Apalache!ConstCardinality IR operator. */
  public static final TlaOper CONST_CARDINALITY = ApalacheOper.constCard$.MODULE$;

  /** The Apalache!MkSeq IR operator. */
  public static final TlaOper MK_SEQ = ApalacheOper.mkSeq$.MODULE$;

  /** The Apalache!ApaFoldSet IR operator. */
  public static final TlaOper APA_FOLD_SET = ApalacheOper.foldSet$.MODULE$;

  /** The Apalache!ApaFoldSeqLeft IR operator. */
  public static final TlaOper APA_FOLD_SEQ_LEFT = ApalacheOper.foldSeq$.MODULE$;

  /** The Apalache!Repeat IR operator. */
  public static final TlaOper REPEAT = ApalacheOper.repeat$.MODULE$;

  /** The Apalache!SetAsFun IR operator. */
  public static final TlaOper SET_AS_FUN = ApalacheOper.setAsFun$.MODULE$;

  /** The PRIME IR operator. */
  public static final TlaOper PRIME = TlaActionOper.prime$.MODULE$;

  /** The STUTTER IR operator. */
  public static final TlaOper STUTTER = TlaActionOper.stutter$.MODULE$;

  /** The NO_STUTTER IR operator. */
  public static final TlaOper NO_STUTTER = TlaActionOper.nostutter$.MODULE$;

  /** The ENABLED IR operator. */
  public static final TlaOper ENABLED = TlaActionOper.enabled$.MODULE$;

  /** The UNCHANGED IR operator. */
  public static final TlaOper UNCHANGED = TlaActionOper.unchanged$.MODULE$;

  /** The COMPOSE IR operator. */
  public static final TlaOper COMPOSE = TlaActionOper.composition$.MODULE$;

  /** The PLUS IR operator. */
  public static final TlaOper PLUS = TlaArithOper.plus$.MODULE$;

  /** The UNARY_MINUS IR operator. */
  public static final TlaOper UNARY_MINUS = TlaArithOper.uminus$.MODULE$;

  /** The MINUS IR operator. */
  public static final TlaOper MINUS = TlaArithOper.minus$.MODULE$;

  /** The MULT IR operator. */
  public static final TlaOper MULT = TlaArithOper.mult$.MODULE$;

  /** The DIV IR operator. */
  public static final TlaOper DIV = TlaArithOper.div$.MODULE$;

  /** The MOD IR operator. */
  public static final TlaOper MOD = TlaArithOper.mod$.MODULE$;

  /** The REAL_DIV IR operator. */
  public static final TlaOper REAL_DIV = TlaArithOper.realDiv$.MODULE$;

  /** The POW IR operator. */
  public static final TlaOper POW = TlaArithOper.exp$.MODULE$;

  /** The INT_RANGE IR operator. */
  public static final TlaOper INT_RANGE = TlaArithOper.dotdot$.MODULE$;

  /** The LT IR operator. */
  public static final TlaOper LT = TlaArithOper.lt$.MODULE$;

  /** The GT IR operator. */
  public static final TlaOper GT = TlaArithOper.gt$.MODULE$;

  /** The LE IR operator. */
  public static final TlaOper LE = TlaArithOper.le$.MODULE$;

  /** The GE IR operator. */
  public static final TlaOper GE = TlaArithOper.ge$.MODULE$;

  /** The AND IR operator. */
  public static final TlaOper AND = TlaBoolOper.and$.MODULE$;

  /** The OR IR operator. */
  public static final TlaOper OR = TlaBoolOper.or$.MODULE$;

  /** The NOT IR operator. */
  public static final TlaOper NOT = TlaBoolOper.not$.MODULE$;

  /** The IMPLIES IR operator. */
  public static final TlaOper IMPLIES = TlaBoolOper.implies$.MODULE$;

  /** The EQUIV IR operator. */
  public static final TlaOper EQUIV = TlaBoolOper.equiv$.MODULE$;

  /** The FORALL3 IR operator. */
  public static final TlaOper FORALL3 = TlaBoolOper.forall$.MODULE$;

  /** The FORALL2 IR operator. */
  public static final TlaOper FORALL2 = TlaBoolOper.forallUnbounded$.MODULE$;

  /** The EXISTS3 IR operator. */
  public static final TlaOper EXISTS3 = TlaBoolOper.exists$.MODULE$;

  /** The EXISTS2 IR operator. */
  public static final TlaOper EXISTS2 = TlaBoolOper.existsUnbounded$.MODULE$;

  /** The CASE IR operator. */
  public static final TlaOper CASE = TlaControlOper.caseNoOther$.MODULE$;

  /** The CASE_OTHER IR operator. */
  public static final TlaOper CASE_OTHER = TlaControlOper.caseWithOther$.MODULE$;

  /** The IF_THEN_ELSE IR operator. */
  public static final TlaOper IF_THEN_ELSE = TlaControlOper.ifThenElse$.MODULE$;

  /** The FiniteSets!IsFiniteSet IR operator. */
  public static final TlaOper IS_FINITE_SET = TlaFiniteSetOper.isFiniteSet$.MODULE$;

  /** The FiniteSets!Cardinality IR operator. */
  public static final TlaOper CARDINALITY = TlaFiniteSetOper.cardinality$.MODULE$;

  /** The RECORD IR operator. */
  public static final TlaOper RECORD = TlaFunOper.rec$.MODULE$;

  /** The TUPLE IR operator. */
  public static final TlaOper TUPLE = TlaFunOper.tuple$.MODULE$;

  /** The FUN_APP IR operator. */
  public static final TlaOper FUN_APP = TlaFunOper.app$.MODULE$;

  /** The DOMAIN IR operator. */
  public static final TlaOper DOMAIN = TlaFunOper.domain$.MODULE$;

  /** The FUN_CTOR IR operator. */
  public static final TlaOper FUN_CTOR = TlaFunOper.funDef$.MODULE$;

  /** The FUN_REC_CTOR IR operator. */
  public static final TlaOper FUN_REC_CTOR = TlaFunOper.recFunDef$.MODULE$;

  /** The FUN_REC_REF IR operator. */
  public static final TlaOper FUN_REC_REF = TlaFunOper.recFunRef$.MODULE$;

  /** The EXCEPT IR operator. */
  public static final TlaOper EXCEPT = TlaFunOper.except$.MODULE$;

  /** The EQ IR operator. */
  public static final TlaOper EQ = TlaOper.eq$.MODULE$;

  /** The NE IR operator. */
  public static final TlaOper NE = TlaOper.ne$.MODULE$;

  /** The OPER_APP IR operator. */
  public static final TlaOper OPER_APP = TlaOper.apply$.MODULE$;

  /** The CHOOSE3 IR operator. */
  public static final TlaOper CHOOSE3 = TlaOper.chooseBounded$.MODULE$;

  /** The CHOOSE2 IR operator. */
  public static final TlaOper CHOOSE2 = TlaOper.chooseUnbounded$.MODULE$;

  /** The LABEL IR operator. */
  public static final TlaOper LABEL = TlaOper.label$.MODULE$;

  /** The Sequences!Head IR operator. */
  public static final TlaOper HEAD = TlaSeqOper.head$.MODULE$;

  /** The Sequences!Tail IR operator. */
  public static final TlaOper TAIL = TlaSeqOper.tail$.MODULE$;

  /** The Sequences!Append IR operator. */
  public static final TlaOper APPEND = TlaSeqOper.append$.MODULE$;

  /** The Sequences!Concat IR operator. */
  public static final TlaOper CONCAT = TlaSeqOper.concat$.MODULE$;

  /** The Sequences!Len IR operator. */
  public static final TlaOper LEN = TlaSeqOper.len$.MODULE$;

  /** The Sequences!SubSeq IR operator. */
  public static final TlaOper SUB_SEQ = TlaSeqOper.subseq$.MODULE$;

  /** The SET_ENUM IR operator. */
  public static final TlaOper SET_ENUM = TlaSetOper.enumSet$.MODULE$;

  /** The FUN_SET IR operator. */
  public static final TlaOper FUN_SET = TlaSetOper.funSet$.MODULE$;

  /** The RECORD_SET IR operator. */
  public static final TlaOper RECORD_SET = TlaSetOper.recSet$.MODULE$;

  /** The Sequences!Seq IR operator. */
  public static final TlaOper SEQ = TlaSetOper.seqSet$.MODULE$;

  /** The SET_IN IR operator. */
  public static final TlaOper SET_IN = TlaSetOper.in$.MODULE$;

  /** The SET_NOT_IN IR operator. */
  public static final TlaOper SET_NOT_IN = TlaSetOper.notin$.MODULE$;

  /** The SET_UNION2 IR operator. */
  public static final TlaOper SET_UNION2 = TlaSetOper.cup$.MODULE$;

  /** The SET_INTERSECT IR operator. */
  public static final TlaOper SET_INTERSECT = TlaSetOper.cap$.MODULE$;

  /** The SET_SUBSET_EQ IR operator. */
  public static final TlaOper SET_SUBSET_EQ = TlaSetOper.subseteq$.MODULE$;

  /** The SET_MINUS IR operator. */
  public static final TlaOper SET_MINUS = TlaSetOper.setminus$.MODULE$;

  /** The SET_FILTER IR operator. */
  public static final TlaOper SET_FILTER = TlaSetOper.filter$.MODULE$;

  /** The SET_MAP IR operator. */
  public static final TlaOper SET_MAP = TlaSetOper.map$.MODULE$;

  /** The SET_POWERSET IR operator. */
  public static final TlaOper SET_POWERSET = TlaSetOper.powerset$.MODULE$;

  /** The SET_UNARY_UNION IR operator. */
  public static final TlaOper SET_UNARY_UNION = TlaSetOper.union$.MODULE$;

  /** The SET_TIMES IR operator. */
  public static final TlaOper SET_TIMES = TlaSetOper.times$.MODULE$;

  /** The GLOBALLY IR operator. */
  public static final TlaOper GLOBALLY = TlaTempOper.box$.MODULE$;

  /** The EVENTUALLY IR operator. */
  public static final TlaOper EVENTUALLY = TlaTempOper.diamond$.MODULE$;

  /** The LEADS_TO IR operator. */
  public static final TlaOper LEADS_TO = TlaTempOper.leadsTo$.MODULE$;

  /** The GUARANTEES IR operator. */
  public static final TlaOper GUARANTEES = TlaTempOper.guarantees$.MODULE$;

  /** The WEAK_FAIRNESS IR operator. */
  public static final TlaOper WEAK_FAIRNESS = TlaTempOper.weakFairness$.MODULE$;

  /** The STRONG_FAIRNESS IR operator. */
  public static final TlaOper STRONG_FAIRNESS = TlaTempOper.strongFairness$.MODULE$;

  /** The TEMPORAL_EXISTS IR operator. */
  public static final TlaOper TEMPORAL_EXISTS = TlaTempOper.EE$.MODULE$;

  /** The TEMPORAL_FORALL IR operator. */
  public static final TlaOper TEMPORAL_FORALL = TlaTempOper.AA$.MODULE$;

  /** The Variants!Variant IR operator. */
  public static final TlaOper VARIANT = VariantOper.variant$.MODULE$;

  /** The Variants!VariantFilter IR operator. */
  public static final TlaOper VARIANT_FILTER = VariantOper.variantFilter$.MODULE$;

  /** The Variants!VariantTag IR operator. */
  public static final TlaOper VARIANT_TAG = VariantOper.variantTag$.MODULE$;

  /** The Variants!VariantGetOrElse IR operator. */
  public static final TlaOper VARIANT_GET_OR_ELSE = VariantOper.variantGetOrElse$.MODULE$;

  /** The Variants!VariantGetUnsafe IR operator. */
  public static final TlaOper VARIANT_GET_UNSAFE = VariantOper.variantGetUnsafe$.MODULE$;
}
