package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.oper.TlaTempOper
import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}

/**
 * Scope-unsafe builder for `TlaTempOper` expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeTemporalBuilder extends ProtoBuilder {

  /** {{{[]P}}} */
  def box(P: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.box, P)

  /** {{{<>P}}} */
  def diamond(P: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.diamond, P)

  /** {{{P ~> Q}}} */
  def leadsTo(P: TlaEx, Q: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.leadsTo, P, Q)

  /** {{{P -+-> Q}}} */
  def guarantees(P: TlaEx, Q: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.guarantees, P, Q)

  /** {{{WF_x(A)}}} */
  def WF(x: TlaEx, A: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.weakFairness, x, A)

  /** {{{SF_x(A)}}} */
  def SF(x: TlaEx, A: TlaEx): TlaEx = buildBySignatureLookup(TlaTempOper.strongFairness, x, A)

  /**
   * {{{\EE x: P}}}
   * @param x
   *   must be a variable name
   */
  def EE(x: TlaEx, P: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx], s"Expected x to be a variable name, found $x.")
    buildBySignatureLookup(TlaTempOper.EE, x, P)
  }

  /**
   * {{{\AA x: P}}}
   * @param x
   *   must be a variable name
   */
  def AA(x: TlaEx, P: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx], s"Expected x to be a variable name, found $x.")
    buildBySignatureLookup(TlaTempOper.AA, x, P)
  }
}
