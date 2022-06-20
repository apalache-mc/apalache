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
 * Type-unsafe builder for TlaFunOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeFunBuilder extends ProtoBuilder {

  /**
   * Record constructor [ k1 |-> v1, ... , kN |-> vN ]; must have at least 1 key-value pair and all keys must be unique
   */
  protected def _rec(args: (String, TlaEx)*): TlaEx = {
    // the other _recSet does all the require checks
    val flatArgs = args.flatMap { case (k, v) =>
      Seq(ValEx(TlaStr(k))(Typed(StrT1)), v)
    }
    _recMixed(flatArgs: _*)
  }

  /**
   * Alternate call method, where pairs are passed interleaved.
   *
   * @see
   *   _rec[[_rec(args: (String, TlaEx)*)]]
   */
  protected def _recMixed(args: TlaEx*): TlaEx = {
    // All keys must be ValEx(TlaStr(_))
    require(args.nonEmpty)
    require(args.size % 2 == 0)
    val (keys, vals) = TlaOper.deinterleave(args)
    require(keys.forall {
      case ValEx(_: TlaStr) => true
      case _                => false
    })
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

  /** {{{<<t1, ..., tn>>}}} with a tuple-type */
  protected def _tuple(args: TlaEx*): TlaEx = {
    // TlaFunOper.tuple can produce both tuples and sequences, so instead of going through cmpFactory, we
    // just define the tuple-variant signature
    val partialSig: PartialSignature = { seq => TupT1(seq: _*) }
    val sig = completePartial(TlaFunOper.tuple.name, partialSig)
    BuilderUtil.composeAndValidateTypes(TlaFunOper.tuple, sig, args: _*)
  }

  /** {{{<<>>}}} with a sequence type */
  protected def _emptySeq(elemType: TlaType1): TlaEx = OperEx(TlaFunOper.tuple)(Typed(SeqT1(elemType)))

  /** {{{<<t1, ..., tn>>}}} with a sequence-type. Must be nonempty. */
  protected def _seq(args: TlaEx*): TlaEx = {
    require(args.nonEmpty)
    // TlaFunOper.tuple can produce both tuples and sequences, so instead of going through cmpFactory, we
    // just define the seq-variant signature
    val partialSig: PartialSignature = { case h +: tail if tail.forall(_ == h) => SeqT1(h) }
    val sig = completePartial(TlaFunOper.tuple.name, partialSig)
    BuilderUtil.composeAndValidateTypes(TlaFunOper.tuple, sig, args: _*)
  }

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

  //////////////////
  // APP overload //
  //////////////////

  /** f[x] for any Applicative f */
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

  protected def _dom(f: TlaEx): TlaEx =
    buildFromPartialSignature(
        { case Seq(tt) if Applicative.domainElemType(tt).nonEmpty => SetT1(Applicative.domainElemType(tt).get) }
    )(TlaFunOper.domain, f)

  /////////////////////
  // EXCEPT overload //
  /////////////////////

  /** [f EXCEPT !.x = e] for any Applicative f */
  protected def _except(f: TlaEx, x: TlaEx, e: TlaEx): TlaEx = {
    val partialSignature: PartialSignature = {
      // asInstanceOfApplicative verifies that x is a ValEx(_), and not just any domT-typed value
      case Seq(appT, domT, cdmT) if asInstanceOfApplicative(appT, x).contains(Applicative(domT, cdmT)) => appT
    }
    buildFromPartialSignature(partialSignature)(TlaFunOper.except, f, x, e)
  }

}
