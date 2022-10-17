package at.forsyte.apalache.tla.typecomp.json

import at.forsyte.apalache.io.json.JsonDeserializationError
import at.forsyte.apalache.tla.lir.{TlaEx, TlaType1, ValEx, VariantT1}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

/**
 * Invokes the `ScopedBuilder` from an operator application by-name (as is read from JSON files)
 *
 * @author
 *   Jure Kukovec
 */
object BuilderCallByName {
  private def validateExpectedArity[T](oper: TlaOper, args: Seq[T]): Unit = {
    val n = args.length
    if (!oper.isCorrectArity(n)) throw new JsonDeserializationError(s"${oper.name} does not permit $n arguments.")
  }

  private val nameMap = Map(
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
      TlaArithOper.plus.name -> TlaArithOper.plus,
      TlaArithOper.uminus.name -> TlaArithOper.uminus,
      TlaArithOper.minus.name -> TlaArithOper.minus,
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
      TlaFunOper.rec.name -> TlaFunOper.rec,
      TlaFunOper.except.name -> TlaFunOper.except,
      TlaFunOper.funDef.name -> TlaFunOper.funDef,
      TlaFunOper.tuple.name -> TlaFunOper.tuple,
      TlaSeqOper.append.name -> TlaSeqOper.append,
      TlaSeqOper.concat.name -> TlaSeqOper.concat,
      TlaSeqOper.head.name -> TlaSeqOper.head,
      TlaSeqOper.tail.name -> TlaSeqOper.tail,
      TlaSeqOper.len.name -> TlaSeqOper.len,
      TlaSeqOper.subseq.name -> TlaSeqOper.subseq,
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
      TlaSetOper.times.name -> TlaSetOper.times,
      TlaSetOper.union.name -> TlaSetOper.union,
      TlaFunOper.recFunRef.name -> TlaFunOper.recFunRef,
      TlaFunOper.recFunDef.name -> TlaFunOper.recFunDef,
      ApalacheOper.assign.name -> ApalacheOper.assign,
      ApalacheOper.gen.name -> ApalacheOper.gen,
      ApalacheOper.skolem.name -> ApalacheOper.skolem,
      ApalacheOper.expand.name -> ApalacheOper.expand,
      ApalacheOper.constCard.name -> ApalacheOper.constCard,
      ApalacheInternalOper.distinct.name -> ApalacheInternalOper.distinct,
      ApalacheOper.mkSeq.name -> ApalacheOper.mkSeq,
      ApalacheOper.foldSet.name -> ApalacheOper.foldSet,
      ApalacheOper.foldSeq.name -> ApalacheOper.foldSeq,
      ApalacheInternalOper.selectInSet.name -> ApalacheInternalOper.selectInSet,
      ApalacheInternalOper.selectInFun.name -> ApalacheInternalOper.selectInFun,
      ApalacheInternalOper.storeInSet.name -> ApalacheInternalOper.storeInSet,
      ApalacheInternalOper.storeNotInSet.name -> ApalacheInternalOper.storeNotInSet,
      ApalacheInternalOper.storeNotInFun.name -> ApalacheInternalOper.storeNotInFun,
      ApalacheInternalOper.smtMap(TlaBoolOper.and).name -> ApalacheInternalOper.smtMap(TlaBoolOper.and),
      ApalacheInternalOper.smtMap(TlaBoolOper.or).name -> ApalacheInternalOper.smtMap(TlaBoolOper.or),
      ApalacheInternalOper.unconstrainArray.name -> ApalacheInternalOper.unconstrainArray,
      ApalacheOper.setAsFun.name -> ApalacheOper.setAsFun,
      ApalacheOper.guess.name -> ApalacheOper.guess,
      VariantOper.variant.name -> VariantOper.variant,
      VariantOper.variantTag.name -> VariantOper.variantTag,
      VariantOper.variantGetUnsafe.name -> VariantOper.variantGetUnsafe,
      VariantOper.variantGetOrElse.name -> VariantOper.variantGetOrElse,
      VariantOper.variantFilter.name -> VariantOper.variantFilter,
  )

  def apply(operString: String, tt1: TlaType1, args: Seq[TBuilderInstruction]): TBuilderInstruction = {
    val oper = nameMap(operString)
    validateExpectedArity(oper, args)
    oper match {
      case TlaOper.eq =>
        val Seq(x, y) = args
        tla.eql(x, y)
      case TlaOper.ne =>
        val Seq(x, y) = args
        tla.neql(x, y)
      case TlaOper.apply =>
        val h +: t = args
        tla.appOp(h, t: _*)
      case TlaOper.chooseBounded =>
        val Seq(x, set, p) = args
        tla.choose(x, set, p)
      case TlaOper.chooseUnbounded =>
        val Seq(x, p) = args
        tla.choose(x, p)
      case TlaBoolOper.and =>
        tla.and(args: _*)
      case TlaBoolOper.or =>
        tla.or(args: _*)
      case TlaBoolOper.not =>
        val Seq(p) = args
        tla.not(p)
      case TlaBoolOper.implies =>
        val Seq(p, q) = args
        tla.impl(p, q)
      case TlaBoolOper.equiv =>
        val Seq(p, q) = args
        tla.equiv(p, q)
      case TlaBoolOper.forall =>
        val Seq(x, set, p) = args
        tla.forall(x, set, p)
      case TlaBoolOper.exists =>
        val Seq(x, set, p) = args
        tla.exists(x, set, p)
      case TlaBoolOper.forallUnbounded =>
        val Seq(x, p) = args
        tla.forall(x, p)
      case TlaBoolOper.existsUnbounded =>
        val Seq(x, p) = args
        tla.exists(x, p)
      case TlaActionOper.prime =>
        val Seq(ex) = args
        tla.prime(ex)
      case TlaActionOper.stutter =>
        val Seq(a, e) = args
        tla.stutt(a, e)
      case TlaActionOper.nostutter =>
        val Seq(a, e) = args
        tla.nostutt(a, e)
      case TlaActionOper.enabled =>
        val Seq(ex) = args
        tla.enabled(ex)
      case TlaActionOper.unchanged =>
        val Seq(ex) = args
        tla.unchanged(ex)
      case TlaActionOper.composition =>
        val Seq(a, b) = args
        tla.comp(a, b)
      case TlaControlOper.caseNoOther =>
        tla.caseSplitMixed(args: _*)
      case TlaControlOper.caseWithOther =>
        val h +: t = args
        tla.caseOtherMixed(h, t: _*)
      case TlaControlOper.ifThenElse =>
        val Seq(i, t, e) = args
        tla.ite(i, t, e)
      case TlaTempOper.AA =>
        val Seq(x, p) = args
        tla.AA(x, p)
      case TlaTempOper.box =>
        val Seq(p) = args
        tla.box(p)
      case TlaTempOper.diamond =>
        val Seq(p) = args
        tla.diamond(p)
      case TlaTempOper.EE =>
        val Seq(x, p) = args
        tla.EE(x, p)
      case TlaTempOper.guarantees =>
        val Seq(p, q) = args
        tla.guarantees(p, q)
      case TlaTempOper.leadsTo =>
        val Seq(p, q) = args
        tla.leadsTo(p, q)
      case TlaTempOper.strongFairness =>
        val Seq(x, a) = args
        tla.SF(x, a)
      case TlaTempOper.weakFairness =>
        val Seq(x, a) = args
        tla.WF(x, a)
      case TlaArithOper.plus =>
        val Seq(x, y) = args
        tla.plus(x, y)
      case TlaArithOper.uminus =>
        val Seq(x) = args
        tla.uminus(x)
      case TlaArithOper.minus =>
        val Seq(x, y) = args
        tla.minus(x, y)
      case TlaArithOper.mult =>
        val Seq(x, y) = args
        tla.mult(x, y)
      case TlaArithOper.div =>
        val Seq(x, y) = args
        tla.div(x, y)
      case TlaArithOper.mod =>
        val Seq(x, y) = args
        tla.mod(x, y)
      case o @ TlaArithOper.realDiv =>
        throw new JsonDeserializationError(s"${o.name} is not supported.")
      case TlaArithOper.exp =>
        val Seq(x, y) = args
        tla.exp(x, y)
      case TlaArithOper.dotdot =>
        val Seq(x, y) = args
        tla.dotdot(x, y)
      case TlaArithOper.lt =>
        val Seq(x, y) = args
        tla.lt(x, y)
      case TlaArithOper.gt =>
        val Seq(x, y) = args
        tla.gt(x, y)
      case TlaArithOper.le =>
        val Seq(x, y) = args
        tla.le(x, y)
      case TlaArithOper.ge =>
        val Seq(x, y) = args
        tla.ge(x, y)
      case TlaFiniteSetOper.cardinality =>
        val Seq(set) = args
        tla.cardinality(set)
      case TlaFiniteSetOper.isFiniteSet =>
        val Seq(set) = args
        tla.isFiniteSet(set)
      case TlaFunOper.app =>
        val Seq(f, x) = args
        tla.app(f, x)
      case TlaFunOper.domain =>
        val Seq(f) = args
        tla.dom(f)
      case TlaFunOper.rec =>
        tla.recMixed(args: _*)
      case TlaFunOper.except =>
        val h +: t = args
        val tPairs = t.grouped(2).toSeq.map { case Seq(a, b) => (a, b) }
        tla.exceptMany(h, tPairs: _*)
      case TlaFunOper.funDef =>
        val h +: t = args
        tla.funDefMixed(h, t: _*)
      case TlaFunOper.tuple =>
        tla.tuple(args: _*)
      case TlaSeqOper.append =>
        val Seq(s, e) = args
        tla.append(s, e)
      case TlaSeqOper.concat =>
        val Seq(s, t) = args
        tla.concat(s, t)
      case TlaSeqOper.head =>
        val Seq(s) = args
        tla.head(s)
      case TlaSeqOper.tail =>
        val Seq(s) = args
        tla.tail(s)
      case TlaSeqOper.len =>
        val Seq(s) = args
        tla.len(s)
      case TlaSeqOper.subseq =>
        val Seq(s, i, j) = args
        tla.subseq(s, i, j)
      case TlaSetOper.enumSet =>
        if (args.isEmpty) tla.emptySet(tt1)
        else tla.enumSet(args: _*)
      case TlaSetOper.in =>
        val Seq(x, s) = args
        tla.in(x, s)
      case TlaSetOper.notin =>
        val Seq(x, s) = args
        tla.notin(x, s)
      case TlaSetOper.cap =>
        val Seq(s, t) = args
        tla.cap(s, t)
      case TlaSetOper.cup =>
        val Seq(s, t) = args
        tla.cup(s, t)
      case TlaSetOper.filter =>
        val Seq(x, set, p) = args
        tla.filter(x, set, p)
      case TlaSetOper.funSet =>
        val Seq(s, t) = args
        tla.funSet(s, t)
      case TlaSetOper.map =>
        val h +: t = args
        tla.mapMixed(h, t: _*)
      case TlaSetOper.powerset =>
        val Seq(s) = args
        tla.powSet(s)
      case TlaSetOper.recSet =>
        tla.recSetMixed(args: _*)
      case TlaSetOper.seqSet =>
        val Seq(s) = args
        tla.seqSet(s)
      case TlaSetOper.setminus =>
        val Seq(s, t) = args
        tla.setminus(s, t)
      case TlaSetOper.subseteq =>
        val Seq(s, t) = args
        tla.subseteq(s, t)
      case TlaSetOper.times =>
        tla.times(args: _*)
      case TlaSetOper.union =>
        val Seq(s) = args
        tla.union(s)
      case o @ (TlaFunOper.recFunRef | TlaFunOper.recFunDef) =>
        throw new JsonDeserializationError(s"${o.name} is not supported.")
      case ApalacheOper.assign =>
        val Seq(x, e) = args
        tla.assign(x, e)
      case ApalacheOper.gen =>
        val Seq(nEx): Seq[TlaEx] = args
        nEx match {
          case ValEx(TlaInt(n)) =>
            tla.gen(n, tt1)
          // should never happen, for case-completeness
          case _ => throw new JsonDeserializationError(s"${oper.name} requires an integer argument.")
        }
      case ApalacheOper.skolem =>
        val Seq(ex) = args
        tla.skolem(ex)
      case ApalacheOper.expand =>
        val Seq(ex) = args
        tla.expand(ex)
      case ApalacheOper.constCard =>
        val Seq(ex) = args
        tla.constCard(ex)
      case ApalacheInternalOper.distinct =>
        tla.distinct(args: _*)
      case ApalacheOper.mkSeq =>
        val Seq(n, f) = args
        val nEx: TlaEx = n
        nEx match {
          case ValEx(TlaInt(n)) =>
            tla.mkSeq(n, f)
          // should never happen, for case-completeness
          case _ => throw new JsonDeserializationError(s"${oper.name} requires an integer argument.")
        }
      case ApalacheOper.foldSet =>
        val Seq(f, v, s) = args
        tla.foldSet(f, v, s)
      case ApalacheOper.foldSeq =>
        val Seq(f, v, s) = args
        tla.foldSeq(f, v, s)
      case ApalacheInternalOper.selectInSet =>
        val Seq(x, s) = args
        tla.selectInSet(x, s)
      case ApalacheInternalOper.selectInFun =>
        val Seq(x, f) = args
        tla.selectInFun(x, f)
      case ApalacheInternalOper.storeInSet =>
        args match {
          case Seq(x, s)    => tla.storeInSet(x, s)
          case Seq(x, f, y) => tla.storeInSet(x, f, y)
          // should never happen, for case-completeness
          case _ => throw new JsonDeserializationError(s"${oper.name} requires 2 or 3 arguments.")
        }
      case ApalacheInternalOper.storeNotInSet =>
        val Seq(x, s) = args
        tla.storeNotInSet(x, s)
      case ApalacheInternalOper.storeNotInFun =>
        val Seq(x, f) = args
        tla.storeNotInFun(x, f)
      case ApalacheInternalOper.smtMap(oper) =>
        val Seq(s, t) = args
        tla.smtMap(oper, s, t)
      case ApalacheInternalOper.unconstrainArray =>
        val Seq(s) = args
        tla.unconstrainArray(s)
      case ApalacheOper.setAsFun =>
        val Seq(s) = args
        tla.setAsFun(s)
      case ApalacheOper.guess =>
        val Seq(s) = args
        tla.guess(s)
      case VariantOper.variant =>
        require(tt1.isInstanceOf[VariantT1])
        val Seq(t, v) = args
        tla.variant(getStrValue(t), v, tt1.asInstanceOf[VariantT1])
      case VariantOper.variantTag =>
        val Seq(v) = args
        tla.variantTag(v)
      case VariantOper.variantGetUnsafe =>
        val Seq(t, v) = args
        tla.variantGetUnsafe(getStrValue(t), v)
      case VariantOper.variantGetOrElse =>
        val Seq(t, v, d) = args
        tla.variantGetOrElse(getStrValue(t), v, d)
      case VariantOper.variantFilter =>
        val Seq(t, v) = args
        tla.variantFilter(getStrValue(t), v)
    }
  }

  private def getStrValue(ex: TlaEx): String = ex match {
    case ValEx(TlaStr(s)) => s
    case _                => throw new JsonDeserializationError(s"$ex must be a string.")
  }

}
