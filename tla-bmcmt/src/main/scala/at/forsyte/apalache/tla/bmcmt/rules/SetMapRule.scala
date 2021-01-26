package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.MapBase
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Translates a set comprehension { e: x_1 \in S_1, ..., x_k \in S_k }.
  *
  * @author Igor Konnov
  */
class SetMapRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val mapbase = new MapBase(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.map, _*) => true
      case _                          => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.map, mapEx, varsAndSets @ _*) =>
        val varNames = varsAndSets.zipWithIndex.filter(_._2 % 2 == 0).collect {
          case (NameEx(n), _) => n
        }
        val sets = varsAndSets.zipWithIndex.filter(_._2 % 2 == 1).map(_._1)
        mapbase.rewriteSetMapManyArgs(state, mapEx, varNames, sets)

      case _ =>
        throw new RewriterException(
          "%s is not applicable to %s".format(getClass.getSimpleName, state.ex),
          state.ex
        )
    }
  }
}
