package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.oper.TlaTempOper
import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}

/**
 * Type-unsafe builder for TlaTempOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeTempBuilder extends ProtoBuilder {

  /** {{{[]P}}} */
  protected def _box(P: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.box, P)

  /** {{{<>P}}} */
  protected def _diamond(P: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.diamond, P)

  /** {{{P ~> Q}}} */
  protected def _leadsTo(P: TlaEx, Q: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.leadsTo, P, Q)

  /** {{{P -+-> Q}}} */
  protected def _guarantees(P: TlaEx, Q: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.guarantees, P, Q)

  /** {{{WF_x(A)}}} */
  protected def _WF(x: TlaEx, A: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.weakFairness, x, A)

  /** {{{SF_x(A)}}} */
  protected def _SF(x: TlaEx, A: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.strongFairness, x, A)

  /** {{{\EE x: P}}} */
  protected def _EE(x: TlaEx, P: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx])
    buildBySignatureLookup(TlaTempOper.EE, x, P)
  }

  /** {{{\AA x: P}}} */
  protected def _AA(x: TlaEx, P: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx])
    buildBySignatureLookup(TlaTempOper.AA, x, P)
  }
}
