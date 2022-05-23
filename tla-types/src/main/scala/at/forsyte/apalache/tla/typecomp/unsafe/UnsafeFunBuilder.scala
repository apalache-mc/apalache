package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.typecomp.Applicative.asInstanceOfApplicative
import at.forsyte.apalache.tla.typecomp.PartialSignature
import at.forsyte.apalache.tla.typecomp.BuilderUtil.{completePartial, composeAndValidateTypes}

/**
 * Type-unsafe builder for TlaFunOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeFunBuilder extends ProtoBuilder {

  /** {{{(t1, ..., tn) => <<t1, ..., tn>>}}} */
  protected def _tuple(args: TlaEx*): TlaEx = buildBySignatureLookup(TlaFunOper.tuple, args: _*)

  /** [x \in S |-> e] */
  protected def _funDef(e: TlaEx, x: TlaEx, S: TlaEx): TlaEx = buildBySignatureLookup(TlaFunOper.funDef, e, x, S)

  // The rest of the operators are overloaded, so buildBySignatureLookup doesn't work

  /** Like [[buildBySignatureLookup]], except the signatures are passed manually */
  private def buildFromPartialSignature(
      partialSig: PartialSignature
    )(oper: TlaOper,
      args: TlaEx*): TlaEx = {
    composeAndValidateTypes(oper, completePartial(oper.name, partialSig), args: _*)
  }

  ///////////////////
  // APP overloads //
  ///////////////////

  /** f[e] for {{{f: a -> b}}} */
  protected def _appFun(f: TlaEx, e: TlaEx): TlaEx =
    buildFromPartialSignature({ case Seq(FunT1(domT, cdmT), t) if t == domT => cdmT })(TlaFunOper.app, f, e)

  /** tup[i] for {{{tup: <<t1, ..., tn>>, i \in 1..n}}} */
  protected def _appTup(tup: TlaEx, i: TlaEx): TlaEx = {
    val partialSignature = {
      // asInstanceOfApplicative verifies that i is a ValEx(TlaInt(_)), and not just any Int-typed value
      case (tt: TupT1, IntT1) if asInstanceOfApplicative(tt, i).nonEmpty => asInstanceOfApplicative(tt, i).get.toT
    }
    buildFromPartialSignature(partialSignature)(TlaFunOper.app, tup, i)
  }

  /** r.x for {{{r: [a1: v1, ..., an: vn], x \in {"a1", ..., "an"} }}}} */
  protected def _appRec(r: TlaEx, x: TlaEx): TlaEx = {
    val partialSignature = {
      // asInstanceOfApplicative verifies that x is a ValEx(TlaStr(_)), and not just any Str-typed value
      case (rt: RecT1, StrT1) if asInstanceOfApplicative(rt, x).nonEmpty => asInstanceOfApplicative(rt, x).get.toT
    }
    buildFromPartialSignature(partialSignature)(TlaFunOper.app, r, x)
  }

  /** s[i] for {{{s: Seq(t)}}}} */
  protected def _appSeq(s: TlaEx, i: TlaEx): TlaEx =
    buildFromPartialSignature({ case Seq(SeqT1(t), IntT1) => t })(TlaFunOper.app, s, i)

  //////////////////////
  // DOMAIN overloads //
  //////////////////////

  /** DOMAIN f for {{{f: a -> b}}} */
  protected def _domFun(f: TlaEx): TlaEx =
    buildFromPartialSignature({ case Seq(FunT1(a, _)) => SetT1(a) })(TlaFunOper.domain, f)

  /** DOMAIN tup for {{{tup: <<t1,...,tn>>}}} */
  protected def _domTup(tup: TlaEx): TlaEx =
    buildFromPartialSignature({ case Seq(_: TupT1) => SetT1(IntT1) })(TlaFunOper.domain, tup)

  /** DOMAIN r for {{{r: [a1: v1, ..., an: vn]}}} */
  protected def _domRec(r: TlaEx): TlaEx =
    buildFromPartialSignature({ case Seq(_: RecT1) => SetT1(StrT1) })(TlaFunOper.domain, r)

  /** DOMAIN s for {{{s: Seq(t)}}} */
  protected def _domSeq(s: TlaEx): TlaEx =
    buildFromPartialSignature({ case Seq(_: SeqT1) => SetT1(IntT1) })(TlaFunOper.domain, s)

  //////////////////////
  // EXCEPT overloads //
  //////////////////////

  /** [f EXCEPT ![x] = e] for {{{f: a -> b}}} */
  protected def _exceptFun(f: TlaEx, x: TlaEx, e: TlaEx): TlaEx =
    buildFromPartialSignature(
        { case Seq(funT @ FunT1(a, b), aa, bb) if a == aa && b == bb => funT }
    )(TlaFunOper.except, f, x, e)

  /** [tup EXCEPT ![i] = e] for {{{tup: <<t1, ..., tn>>, i \in 1..n}}} */
  protected def _exceptTup(tup: TlaEx, i: TlaEx, e: TlaEx): TlaEx = {
    val partialSignature = {
      // asInstanceOfApplicative verifies that i is a ValEx(TlaInt(_)), and not just any Int-typed value
      case (tt: TupT1, IntT1, t) if asInstanceOfApplicative(tt, i).exists(_.toT == t) => tt
    }
    buildFromPartialSignature(partialSignature)(TlaFunOper.except, tup, i, e)
  }

  /** [r EXCEPT !.x = e] for {{{r: [a1: v1, ..., an: vn], x \in {"a1", ..., "an"} }}}} */
  protected def _exceptRec(r: TlaEx, x: TlaEx, e: TlaEx): TlaEx = {
    val partialSignature = {
      // asInstanceOfApplicative verifies that x is a ValEx(TlaStr(_)), and not just any Str-typed value
      case (rt: RecT1, StrT1, t) if asInstanceOfApplicative(rt, x).exists(_.toT == t) => rt
    }
    buildFromPartialSignature(partialSignature)(TlaFunOper.except, r, x, e)
  }

  /** [s EXCEPT ![i] = e] for {{{s: Seq(t)}}}} */
  protected def _exceptSeq(s: TlaEx, i: TlaEx, e: TlaEx): TlaEx =
    buildFromPartialSignature({ case Seq(seqT @ SeqT1(t), IntT1, tt) if t == tt => seqT })(TlaFunOper.except, s, i, e)

}
