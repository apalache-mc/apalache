package at.forsyte.apalache.tla.lir.aux

import at.forsyte.apalache.tla.lir.{FunT1, NameEx, OperEx, OperT1, TlaEx, Typed}
import at.forsyte.apalache.tla.lir.oper.TlaOper

/**
 * <p>This is a temporary kludge to support migration from TLC's :> and @@. Do not use it in the new code.
 * This will be fixed in: https://github.com/informalsystems/apalache/issues/1226</p>
 *
 * <p>The name of this object suggests that it will disappear soon ;-)</p>
 */
object SmileyFunFun {

  /**
   * A temporary builder for ":>"
   *
   * @param funT1 the function type
   * @param key   the key expression
   * @param value the value expression
   * @return operator application for ":>"
   */
  def smiley(funT1: FunT1, key: TlaEx, value: TlaEx): TlaEx = {
    val smileyType = OperT1(Seq(funT1.arg, funT1.res), funT1)
    OperEx(TlaOper.apply, NameEx(":>")(Typed(smileyType)), key, value)(Typed(funT1))
  }

  /**
   * A temporary builder for "@@"
   *
   * @param funT1 the function type
   * @param f1    function on the left-hand side
   * @param f2    function on the right-hand side
   * @return operator application for "@@"
   */
  def funfun(funT1: FunT1, f1: TlaEx, f2: TlaEx): TlaEx = {
    val funfunType = OperT1(Seq(funT1, funT1), funT1)
    OperEx(TlaOper.apply, NameEx("@@")(Typed((funfunType))), f1, f2)(Typed(funT1))
  }
}
