package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.typecomp.BuilderUtil

/**
 * Scope-unsafe builder for TlaBoolOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
class UnsafeBoolBuilder extends ProtoBuilder {

  /** {{{args[0] /\ ... /\ args[n]}}} */
  def and(args: TlaEx*): TlaEx = buildBySignatureLookup(TlaBoolOper.and, args: _*)

  /** {{{args[0] \/ ... \/ args[n]}}} */
  def or(args: TlaEx*): TlaEx = buildBySignatureLookup(TlaBoolOper.or, args: _*)

  /** {{{~p}}} */
  def not(p: TlaEx): TlaEx = buildBySignatureLookup(TlaBoolOper.not, p)

  /** {{{p => q}}} */
  def impl(p: TlaEx, q: TlaEx): TlaEx = buildBySignatureLookup(TlaBoolOper.implies, p, q)

  /** {{{p <=> q}}} */
  def equiv(p: TlaEx, q: TlaEx): TlaEx = buildBySignatureLookup(TlaBoolOper.equiv, p, q)

  /**
   * {{{\A x \in set: p}}}
   * @param x
   *   must be a variable name
   */
  def forall(x: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    BuilderUtil.getBoundVarsOrThrow(x)
    buildBySignatureLookup(TlaBoolOper.forall, x, set, p)
  }

  /**
   * {{{\A x: p}}}
   * @param x
   *   must be a variable name
   */
  def forall(x: TlaEx, p: TlaEx): TlaEx = {
    BuilderUtil.getBoundVarsOrThrow(x)
    buildBySignatureLookup(TlaBoolOper.forallUnbounded, x, p)
  }

  /**
   * {{{\E x \in set: p}}}
   * @param x
   *   must be a variable name
   */
  def exists(x: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    BuilderUtil.getBoundVarsOrThrow(x)
    buildBySignatureLookup(TlaBoolOper.exists, x, set, p)
  }

  /**
   * {{{\E x: p}}}
   * @param x
   *   must be a variable name
   */
  def exists(x: TlaEx, p: TlaEx): TlaEx = {
    BuilderUtil.getBoundVarsOrThrow(x)
    buildBySignatureLookup(TlaBoolOper.existsUnbounded, x, p)
  }
}
