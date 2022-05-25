package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.typecomp.Applicative.asInstanceOfApplicative
import at.forsyte.apalache.tla.typecomp.{Applicative, PartialSignature}
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
