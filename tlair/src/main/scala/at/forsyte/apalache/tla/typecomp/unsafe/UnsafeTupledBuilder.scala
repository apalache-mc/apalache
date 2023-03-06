package at.forsyte.apalache.tla.typecomp.unsafe
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.typecomp.BuilderUtil

/**
 * Scope-unsafe builder for syntax-sugar.
 *
 * @author
 *   Jure Kukovec
 */
class UnsafeTupledBuilder extends ProtoBuilder {

  /**
   * {{{\A vars \in set: p}}}
   * @param vars
   *   must be a variable name or a tuple of variable names
   */
  def forallAllowTuples(vars: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    BuilderUtil.getBoundVarsOrThrow(vars)
    buildBySignatureLookup(TlaBoolOper.forall, vars, set, p)
  }

  /**
   * {{{\A vars: p}}}
   * @param vars
   *   must be a variable name or a tuple of variable names
   */
  def forallAllowTuples(vars: TlaEx, p: TlaEx): TlaEx = {
    BuilderUtil.getBoundVarsOrThrow(vars)
    buildBySignatureLookup(TlaBoolOper.forallUnbounded, vars, p)
  }

  /**
   * {{{\E vars \in set: p}}}
   * @param vars
   *   must be a variable name or a tuple of variable names
   */
  def existsAllowTuples(vars: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    BuilderUtil.getBoundVarsOrThrow(vars)
    buildBySignatureLookup(TlaBoolOper.exists, vars, set, p)
  }

  /**
   * {{{\E vars: p}}}
   * @param vars
   *   must be a variable name or a tuple of variable names
   */
  def existsAllowTuples(vars: TlaEx, p: TlaEx): TlaEx = {
    BuilderUtil.getBoundVarsOrThrow(vars)
    buildBySignatureLookup(TlaBoolOper.existsUnbounded, vars, p)
  }
}
