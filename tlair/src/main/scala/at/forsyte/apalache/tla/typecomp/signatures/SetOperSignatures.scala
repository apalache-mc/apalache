package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, SeqT1, SetT1, TupT1}
import at.forsyte.apalache.tla.lir.oper.{AnyPositiveArity, TlaSetOper}
import at.forsyte.apalache.tla.typecomp.BuilderUtil
import at.forsyte.apalache.tla.typecomp.{PartialSignature, SignatureMap}

/**
 * Produces a SignatureMap for all set operators
 *
 * @author
 *   Jure Kukovec
 */
object SetOperSignatures {
  import TlaSetOper._
  import BuilderUtil._

  /**
   * Returns a map that assigns a signature generator to each TlaSetOper. Because most operators are polymorphic, their
   * signatures will contain type variables produced on-demand by varPool.
   */
  def getMap: SignatureMap = {

    // \cup, \cap, \ are binary, polymorphic and symm (w.r.t. arg types)
    // (Set(t), Set(t)) => Set(t)
    val binarySymm: SignatureMap = Seq(
        cup,
        cap,
        setminus,
    ).map { signatureMapEntry(_, { case Seq(st @ SetT1(t), SetT1(tt)) if t == tt => st }) }.toMap

    // \in, \notin are similar, but asymm w.r.t arg types
    // (t, Set(t)) => Bool
    val binaryAsymm: SignatureMap = Seq(
        in,
        notin,
    ).map { signatureMapEntry(_, { case Seq(t, SetT1(tt)) if t == tt => BoolT1 }) }.toMap

    val mapPartial: PartialSignature = {
      case t +: pairs if pairs.nonEmpty && pairs.size % 2 == 0 && pairs.grouped(2).forall {
            case Seq(tt, SetT1(tt2)) => tt == tt2
            case _                   => false
          } =>
        SetT1(t)
    }

    // map is polyadic, with 2k + 1 args in general
    // (t, t1, Set(t1), ..., tk, Set(tk)) => Set(t)
    val mapSig = signatureMapEntry(map, mapPartial)

    // { x \in S: p } is polymorphic
    // (t, Set(t), Bool) => Set(t)
    val filterSig = signatureMapEntry(filter, { case Seq(t, st @ SetT1(tt), BoolT1) if t == tt => st })

    // recSet does NOT have a signature (the return type depends on the field value)

    // Seq(S) is polymorphic, fixed arity 1
    // (Set(t)) => Set(Seq(t))
    val seqSetSig = signatureMapEntry(seqSet, { case Seq(SetT1(t)) => SetT1(SeqT1(t)) })

    // SUBSET S is polymorphic, fixed arity 1
    // (Set(t)) => Set(Set(t))
    val powSetSig = signatureMapEntry(powerset, { case Seq(st: SetT1) => SetT1(st) })

    val timesPartial: PartialSignature = {
      case SetT1(t1) +: SetT1(t2) +: rest if rest.forall(_.isInstanceOf[SetT1]) =>
        val ts = rest.map {
          case SetT1(t) => t
          case t        => t // impossible, but needed for warning suppression
        }
        SetT1(TupT1(t1 +: t2 +: ts: _*))
    }

    // \X is polyadic with n = 2 + k args
    // (Set(t1), ..., Set(tn)) => Set(<<t1,...,tn>>)
    val timesSig = signatureMapEntry(times, timesPartial)

    // [_ -> _] is polymorphic
    // (Set(t1), Set(t2)) => Set(t1 -> t2)
    val funSetSig = signatureMapEntry(funSet, { case Seq(SetT1(t1), SetT1(t2)) => SetT1(FunT1(t1, t2)) })

    // UNION is polymorphic, fixed arity 1
    // (Set(Set(t))) => Set(t)
    val unionSig = signatureMapEntry(union, { case Seq(SetT1(st: SetT1)) => st })

    // { _ } is polyadic
    // (t, ..., t) => Set(t)
    // We force a check against AnyPositiveArity, as the empty set is not built by an enumSet call.
    // This should be caught by a require(_) in the builder method ahead of time, but having fallback
    // sanity checking here helps with bugfixing.
    val enumSig =
      enumSet -> checkForArityException(enumSet.name, AnyPositiveArity(),
          { case t +: ts if ts.forall(_ == t) => SetT1(t) })

    // \subseteq is polymorphic
    // (Set(t), Set(t)) => Bool
    val subseteqSig = signatureMapEntry(subseteq, { case Seq(SetT1(t), SetT1(tt)) if t == tt => BoolT1 })

    val rest: SignatureMap = Seq(
        mapSig,
        filterSig,
        seqSetSig,
        powSetSig,
        timesSig,
        funSetSig,
        unionSig,
        enumSig,
        subseteqSig,
    ).toMap

    binarySymm ++ binaryAsymm ++ rest
  }
}
