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
class UnsafeFunBuilder extends ProtoBuilder {

  // We borrow the LiteralBuilder to make TLA strings from Scala strings
  private val strBuilder = new UnsafeLiteralAndNameBuilder
  private def mkTlaStr: String => TlaEx = strBuilder.str

  private def formRecordFieldType(args: Seq[TlaEx]): SortedMap[String, TlaType1] = {
    require(TlaFunOper.rec.arity.cond(args.size), s"Expected args to have even, positive arity, found $args.")
    // All keys must be ValEx(TlaStr(_))
    val (keys, _) = TlaOper.deinterleave(args)
    require(keys.forall {
          case ValEx(_: TlaStr) => true
          case _                => false
        }, s"Expected keys to be TLA+ strings, found $keys.")
    // Keys must be unique
    val duplicates = keys.filter(k => keys.count(_ == k) > 1)
    require(duplicates.isEmpty, s"Expected keys to be unique, found duplicates: ${duplicates.mkString(", ")}.")

    // We don't need a dynamic TypeComputation, because a record constructor admits all types (we've already validated
    // all keys as strings with `require`)
    val keyTypeMap = args
      .grouped(2)
      .map {
        case Seq(ValEx(TlaStr(s)), ex) => (s -> ex.typeTag.asTlaType1())
        case _ => // Impossible, but need to suppress warning
          throw new IllegalArgumentException("record field must be a TLA string")
      }
      .toSeq

    SortedMap(keyTypeMap: _*)
  }

  /**
   * Like [[rec]] but with a `RowRecT1` types
   *
   * @param rowVar
   *   The name of a free row variable
   */
  def rowRec(rowVar: Option[VarT1], args: (String, TlaEx)*): TlaEx = {
    // _recMixed does all the require checks
    val flatArgs = args.flatMap { case (k, v) =>
      Seq(mkTlaStr(k), v)
    }
    rowRecMixed(rowVar, flatArgs: _*)
  }

  /**
   * Like [[recMixed]] but with a `RowRecT1` types
   *
   * @param rowVar
   *   The name of a free row variable
   */
  def rowRecMixed(rowVar: Option[VarT1], args: TlaEx*): TlaEx = {
    val fieldTypes = formRecordFieldType(args)
    val recType = RecRowT1(RowT1(fieldTypes, rowVar))
    OperEx(TlaFunOper.rec, args: _*)(Typed(recType))
  }

  /**
   * {{{[ args[0]._1 |-> args[0]._2, ..., args[n]._1 |-> args[n]._2 ]}}}
   * @param args
   *   must be nonempty, and all keys must be unique strings
   */
  def rec(args: (String, TlaEx)*): TlaEx = {
    // _recMixed does all the require checks
    val flatArgs = args.flatMap { case (k, v) =>
      Seq(mkTlaStr(k), v)
    }
    recMixed(flatArgs: _*)
  }

  /**
   * {{{[ args[0] |-> args[1], ..., args[n-1] |-> args[n] ]}}}
   * @param args
   *   must have even, positive arity, and all keys must be unique strings
   */
  def recMixed(args: TlaEx*): TlaEx = {
    val fieldTypes = formRecordFieldType(args)
    val recType = RecT1(fieldTypes)
    OperEx(TlaFunOper.rec, args: _*)(Typed(recType))
  }

  /** {{{<<args[0], ..., args[n]>> : <<t1, ..., tn>>}}} */
  def tuple(args: TlaEx*): TlaEx = {
    // TlaFunOper.tuple can produce both tuples and sequences, so instead of going through cmpFactory, we
    // just define the tuple-variant signature
    val partialSig: PartialSignature = { seq => TupT1(seq: _*) }
    val sig = completePartial(TlaFunOper.tuple.name, partialSig)
    BuilderUtil.composeAndValidateTypes(TlaFunOper.tuple, sig, args: _*)
  }

  /** {{{<<>> : Seq(t)}}} */
  def emptySeq(t: TlaType1): TlaEx = OperEx(TlaFunOper.tuple)(Typed(SeqT1(t)))

  /**
   * {{{<<args[0], ..., args[n]>> : Seq(t)}}}
   * @param args
   *   must be nonempty.
   */
  def seq(args: TlaEx*): TlaEx = {
    require(args.nonEmpty, s"args must be nonempty.")
    // TlaFunOper.tuple can produce both tuples and sequences, so instead of going through cmpFactory, we
    // just define the seq-variant signature
    val partialSig: PartialSignature = { case h +: tail if tail.forall(_ == h) => SeqT1(h) }
    val sig = completePartial(TlaFunOper.tuple.name, partialSig)
    BuilderUtil.composeAndValidateTypes(TlaFunOper.tuple, sig, args: _*)
  }

  /**
   * {{{[pairs[0]._1 \in pairs[0]._2, ..., pairs[n]._1 \in pairs[n]._2 |-> e]}}}
   * @param pairs
   *   must be nonempty, and all vars must be unique variable names
   */
  def funDef(e: TlaEx, pairs: (TlaEx, TlaEx)*): TlaEx = {
    // _funDefMixed does all the require checks
    val args = pairs.flatMap { case (k, v) =>
      Seq(k, v)
    }
    funDefMixed(e, args: _*)
  }

  /**
   * {{{[pairs[0] \in pairs[1], ..., pairs[n-1] \in pairs[n] |-> e]}}}
   * @param pairs
   *   must have even, positive arity, and all vars must be unique variable names
   */
  def funDefMixed(e: TlaEx, pairs: TlaEx*): TlaEx = {
    // Even, non-zero number of args in `pairs` and every other argument is NameEx
    require(TlaFunOper.funDef.arity.cond(1 + pairs.size), s"Expected pairs to have even, positive arity, found $pairs.")
    val (vars, _) = TlaOper.deinterleave(pairs)
    require(vars.forall { _.isInstanceOf[NameEx] }, s"Expected vars to be variable names, found $vars.")
    // Vars must be unique
    val duplicates = vars.filter(k => vars.count(_ == k) > 1)
    require(duplicates.isEmpty, s"Expected vars to be unique, found duplicates: ${duplicates.mkString(", ")}.")
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

  /**
   * {{{f[x]}}}
   * @param f
   *   must be [[Applicative]]
   */
  def app(f: TlaEx, x: TlaEx): TlaEx = {
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

  /**
   * {{{DOMAIN f}}}
   * @param f
   *   must be [[Applicative]]
   */
  def dom(f: TlaEx): TlaEx =
    buildFromPartialSignature(
        { case Seq(tt) if Applicative.domainElemType(tt).nonEmpty => SetT1(Applicative.domainElemType(tt).get) }
    )(TlaFunOper.domain, f)

  /////////////////////
  // EXCEPT overload //
  /////////////////////

  /**
   * {{{[f EXCEPT ![x] = e]}}}
   * @param f
   *   must be [[Applicative]]
   */
  def except(f: TlaEx, x: TlaEx, e: TlaEx): TlaEx = {

    // EXCEPT requires arguments to be wrapped in a tuple, i.e. [<<x>>]
    def tuplifyAppT(t: TlaType1): Option[Applicative] = asInstanceOfApplicative(t, x).map {
      case Applicative(fromT, toT) => Applicative(TupT1(fromT), toT)
    }

    val partialSignature: PartialSignature = {
      // asInstanceOfApplicative verifies that x is a ValEx(_), and not just any domT-typed value
      case Seq(appT, domT, cdmT) if tuplifyAppT(appT).contains(Applicative(domT, cdmT)) => appT
    }

    buildFromPartialSignature(partialSignature)(TlaFunOper.except, f, tuple(x), e)
  }

}
