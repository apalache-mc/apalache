package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.rules.support.SetEmptiness
import at.forsyte.apalache.tla.bmcmt.rules.support.SetEmptiness.StaticallyEmpty
import at.forsyte.apalache.tla.bmcmt.types.FinFunSetT
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.types.{BuilderUT => BuilderT, tlaU => tla}

/**
 * This rule constructs a cell for a function set [S -> T]. Nontrivial function sets stay unexpanded and point to S and
 * T. Function sets with a definitely empty operand are represented as an ordinary empty or singleton set.
 *
 * @author
 *   Igor Konnov
 */
class FunSetCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val simplifier = new ConstSimplifierForSmt

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.funSet, _, _) => true
      case _                               => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case funSetEx @ OperEx(TlaSetOper.funSet, domEx, cdmEx) =>
        // switch to cell theory
        var nextState = rewriter.rewriteUntilDone(state.setRex(domEx))
        val dom = nextState.asCell
        nextState = rewriter.rewriteUntilDone(nextState.setRex(cdmEx))
        val cdm = nextState.asCell

        val funT = TlaType1.fromTypeTag(funSetEx.typeTag) match {
          case SetT1(ft @ FunT1(_, _)) => ft
          case t                       =>
            throw new TypingException(s"Function-set $funSetEx should have a set-of-functions type, found: $t",
                funSetEx.ID)
        }

        (SetEmptiness(nextState, dom), SetEmptiness(nextState, cdm)) match {
          // There is exactly one function over the empty domain, independently of the co-domain.
          case (StaticallyEmpty, _) =>
            makeSingletonWhen(nextState, funT, tla.bool(true))

          // [S -> {}] contains the empty function exactly when S is empty.
          case (domEmptiness, StaticallyEmpty) =>
            makeSingletonWhen(nextState, funT, domEmptiness.predicate)

          // the default case: rewrite to a special cell without expanding the set of functions
          case _ =>
            // This is an unexpanded set, not an empty array. LazyEquality constrains its equality semantics.
            val arena = nextState.arena.appendCellOld(FinFunSetT(dom.cellType, cdm.cellType), isUnconstrained = true)
            val newCell = arena.topCell
            val newArena = arena
              .setDom(newCell, dom)
              .setCdm(newCell, cdm)
            nextState.setArena(newArena).setRex(newCell.toNameEx)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  /** Construct either an empty set or a singleton containing the canonical empty function. */
  private def makeSingletonWhen(state: SymbState, funT: FunT1, condition: BuilderT): SymbState = {
    val simplifiedCondition = simplifier.applySimplifyShallowToBuilderEx(condition)
    var nextState = state.updateArena(_.appendCell(SetT1(funT)))
    val setCell = nextState.arena.topCell

    if (simplifier.isFalseConst(simplifiedCondition)) {
      return nextState.setRex(setCell.toBuilder)
    }

    val (arenaWithEmptyFun, emptyFun) = rewriter.defaultValueCache.getOrCreate(nextState.arena, funT)
    nextState = nextState.setArena(arenaWithEmptyFun)

    val ptr =
      if (simplifier.isTrueConst(simplifiedCondition)) FixedElemPtr(emptyFun)
      else SmtExprElemPtr(emptyFun, simplifiedCondition)
    nextState = nextState.updateArena(_.appendHas(setCell, ptr))

    val inSet = tla.storeInSet(emptyFun.toBuilder, setCell.toBuilder)
    if (simplifier.isTrueConst(simplifiedCondition)) {
      rewriter.solverContext.assertGroundExpr(inSet)
    } else {
      val notInSet = tla.storeNotInSet(emptyFun.toBuilder, setCell.toBuilder)
      rewriter.solverContext.assertGroundExpr(tla.ite(simplifiedCondition, inSet, notInSet))
    }

    nextState.setRex(setCell.toBuilder)
  }
}
