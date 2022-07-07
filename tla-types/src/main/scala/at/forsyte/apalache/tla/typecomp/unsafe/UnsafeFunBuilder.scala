package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.typecomp.Applicative.asInstanceOfApplicative
import at.forsyte.apalache.tla.typecomp.{Applicative, BuilderUtil, PartialSignature}
import at.forsyte.apalache.tla.typecomp.BuilderUtil.{completePartial, composeAndValidateTypes}

import scala.collection.immutable.SortedMap

/**
 * Scope-unsafe builder for TlaFunOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeFunBuilder extends ProtoBuilder {

  /**
   * {{{[ args[0]._1 |-> args[0]._2, ..., args[n]._1 |-> args[n]._2 ]}}} `args` must be nonempty, and all keys must be
   * unique strings
   */
  protected def _rec(args: (String, TlaEx)*): TlaEx = {
    // _recMixed does all the require checks
    val flatArgs = args.flatMap { case (k, v) =>
      Seq(ValEx(TlaStr(k))(Typed(StrT1)), v)
    }
    _recMixed(flatArgs: _*)
  }

  /**
   * {{{[ args[0] |-> args[1], ..., args[n-1] |-> args[n] ]}}} `args` must have even, positive arity, and all keys must
   * be unique strings
   */
  protected def _recMixed(args: TlaEx*): TlaEx = {
    require(TlaFunOper.rec.arity.cond(args.size))
    // All keys must be ValEx(TlaStr(_))
    val (keys, vals) = TlaOper.deinterleave(args)
    require(keys.forall {
      case ValEx(_: TlaStr) => true
      case _                => false
    })
    // Keys must be unique
    val duplicates = keys.filter(k => keys.count(_ == k) > 1)
    if (duplicates.nonEmpty)
      throw new IllegalArgumentException(s"Found repeated keys in record constructor: ${duplicates.mkString(", ")}")

    // We don't need a dynamic TypeComputation, because a record constructor admits all types (we've already validated
    // all keys as strings with `require`)

    val keyTypeMap = keys.zip(vals).foldLeft(SortedMap.empty[String, TlaType1]) {
      case (map, (ValEx(TlaStr(s)), ex)) =>
        map + (s -> ex.typeTag.asTlaType1())
      case (map, _) => // Impossible, but need to suppress warning
        map
    }

    val recType = RecT1(keyTypeMap)

    OperEx(TlaFunOper.rec, args: _*)(Typed(recType))
  }

  /** {{{<<args[0], ..., args[n]>> : <<t1, ..., tn>>}}} */
  protected def _tuple(args: TlaEx*): TlaEx = {
    // TlaFunOper.tuple can produce both tuples and sequences, so instead of going through cmpFactory, we
    // just define the tuple-variant signature
    val partialSig: PartialSignature = { seq => TupT1(seq: _*) }
    val sig = completePartial(TlaFunOper.tuple.name, partialSig)
    BuilderUtil.composeAndValidateTypes(TlaFunOper.tuple, sig, args: _*)
  }

  /** {{{<<>> : Seq(t)}}} */
  protected def _emptySeq(t: TlaType1): TlaEx = OperEx(TlaFunOper.tuple)(Typed(SeqT1(t)))

  /** {{{<<args[0], ..., args[0]>> : Seq(t)}}} `args` must be nonempty. */
  protected def _seq(args: TlaEx*): TlaEx = {
    require(args.nonEmpty)
    // TlaFunOper.tuple can produce both tuples and sequences, so instead of going through cmpFactory, we
    // just define the seq-variant signature
    val partialSig: PartialSignature = { case h +: tail if tail.forall(_ == h) => SeqT1(h) }
    val sig = completePartial(TlaFunOper.tuple.name, partialSig)
    BuilderUtil.composeAndValidateTypes(TlaFunOper.tuple, sig, args: _*)
  }

  /**
   * {{{[pairs[0]._1 \in pairs[0]._2, ..., pairs[n]._1 \in pairs[n]._2 |-> e]}}} `pairs` must be nonempty, and all vars
   * must be unique variable names
   */
  protected def _funDef(e: TlaEx, pairs: (TlaEx, TlaEx)*): TlaEx = {
    // _funDefMixed does all the require checks
    val args = pairs.flatMap { case (k, v) =>
      Seq(k, v)
    }
    _funDefMixed(e, args: _*)
  }

  /**
   * {{{[pairs[0] \in pairs[1], ..., pairs[n-1] \in pairs[n] |-> e]}}} `pairs` must have even, positive arity, and all
   * vars must be unique variable names
   */
  protected def _funDefMixed(e: TlaEx, pairs: TlaEx*): TlaEx = {
    // Even, non-zero number of args in `pairs` and every other argument is NameEx
    require(TlaFunOper.funDef.arity.cond(1 + pairs.size))
    val (vars, _) = TlaOper.deinterleave(pairs)
    require(vars.forall { _.isInstanceOf[NameEx] })
    // Vars must be unique
    val duplicates = vars.filter(k => vars.count(_ == k) > 1)
    if (duplicates.nonEmpty) {
      throw new IllegalArgumentException(s"Found repeated keys in record constructor: ${duplicates.mkString(", ")}")
    }
    buildBySignatureLookup(TlaFunOper.funDef, e +: pairs: _*)
  }

  // The rest of the operators are overloaded, so buildBySignatureLookup doesn't work

  /** Like [[buildBySignatureLookup]], except the signatures are passed manually */
  private def buildFromPartialSignature(
      partialSig: PartialSignature
    )(oper: TlaOper,
      args: TlaEx*): TlaEx = {
    composeAndValidateTypes(oper, completePartial(oper.name, partialSig), args: _*)
  }

  //////////////////
  // APP overload //
  //////////////////

  /** {{{f[x]}}} for any Applicative `f` */
  protected def _app(f: TlaEx, x: TlaEx): TlaEx = {
    val partialSignature: PartialSignature = {
      // asInstanceOfApplicative verifies that x is a ValEx(_), and not just any domT-typed value
      case Seq(appT, domT) if asInstanceOfApplicative(appT, x).exists(_.fromT == domT) =>
        asInstanceOfApplicative(appT, x).get.toT
    }
    buildFromPartialSignature(partialSignature)(TlaFunOper.app, f, x)
  }

  /////////////////////
  // DOMAIN overload //
  /////////////////////

  /** {{{DOMAIN f}}} for any Applicative `f` */
  protected def _dom(f: TlaEx): TlaEx =
    buildFromPartialSignature(
        { case Seq(tt) if Applicative.domainElemType(tt).nonEmpty => SetT1(Applicative.domainElemType(tt).get) }
    )(TlaFunOper.domain, f)

  /////////////////////
  // EXCEPT overload //
  /////////////////////

  /** {{{[f EXCEPT ![x] = e]}}} for any Applicative `f` */
  protected def _except(f: TlaEx, x: TlaEx, e: TlaEx): TlaEx = {
    val partialSignature: PartialSignature = {
      // asInstanceOfApplicative verifies that x is a ValEx(_), and not just any domT-typed value
      case Seq(appT, domT, cdmT) if asInstanceOfApplicative(appT, x).contains(Applicative(domT, cdmT)) => appT
    }
    buildFromPartialSignature(partialSignature)(TlaFunOper.except, f, x, e)
  }

}
