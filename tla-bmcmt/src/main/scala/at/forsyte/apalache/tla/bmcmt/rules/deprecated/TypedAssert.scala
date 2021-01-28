package at.forsyte.apalache.tla.bmcmt.rules.deprecated

import at.forsyte.apalache.tla.bmcmt.types.{CellT, FailPredT}
import at.forsyte.apalache.tla.bmcmt.{SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla

/**
  * In many cases we like to introduce an assertion that fails in case of error and returns a dummy value otherwise.
  * Unfortunately, it does not work with Tlc!Assert, as it returns a value of Boolean type.
  * This class provides us with an implementation that returns a cell of given type.
  *
  * @author Igor Konnov
  *
  * @param rewriter a symbolic rewriter
  */
@deprecated("We do not have clean semantics for assert")
class TypedAssert(rewriter: SymbStateRewriter) {
  def typedAssert(state: SymbState, targetType: CellT, arg: TlaEx, message: String): SymbState = {
    val valueState = rewriter.rewriteUntilDone(state.setRex(arg))
    // introduce an unknown value for the outcome of assert, since this value may be unified in IF-THEN-ELSE
    var arena = valueState.arena.appendCell(targetType)
    val result = arena.topCell
    // introduce a new failure predicate
    arena = arena.appendCell(FailPredT())
    val failPred = arena.topCell
    rewriter.addMessage(failPred.id, "Assertion error: " + message)
    val assertion = valueState.ex
    val constraint = tla.impl(failPred.toNameEx, tla.not(assertion))
    rewriter.solverContext.assertGroundExpr(constraint)
    // return isReachable. If there is a model M s.t. M |= isReachable, then M |= failPred allows us
    // to check, whether the assertion is violated or not
    valueState.setArena(arena).setRex(result.toNameEx)
  }

}
