package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, InOpFactory}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.{TlaBoolSet, TlaIntSet}
import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, IntT1, NameEx, OperEx, TlaEx, TlaType1, ValEx}

/**
 * This rule translates the definition of a recursive function. It is similar to CHOOSE.
 * Unlike CHOOSE, it does not have a fallback option, when the definition has no solution.
 * Hence, an infeasible definition of a recursive function may lead to a deadlock.
 *
 * @author Igor Konnov
 */
class RecFunDefAndRefRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pick = new CherryPick(rewriter)
  private val inOpFactory = new InOpFactory(rewriter.solverContext.config.smtEncoding)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.recFunDef, _*) => true
      case OperEx(TlaFunOper.recFunRef)     => true
      case _                                => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(TlaFunOper.recFunDef, mapEx, NameEx(varName), setEx) =>
        // note that we only have a single-argument case here, as Desugarer collapses multiple arguments into a tuple
        val funT1 = TlaType1.fromTypeTag(ex.typeTag).asInstanceOf[FunT1]
        rewriteFunCtor(state, funT1, mapEx, varName, setEx)

      case OperEx(TlaFunOper.recFunRef) =>
        val name = TlaFunOper.recFunRef.uniqueName
        if (state.binding.contains(name)) {
          state.setRex(state.binding(name).toNameEx)
        } else {
          throw new RewriterException("Referencing a recursive function that is undefined", state.ex)
        }

      case _ =>
        throw new RewriterException(
            "%s is not applicable to %s"
              .format(getClass.getSimpleName, state.ex), state.ex)
    }
  }

  private def rewriteFunCtor(state: SymbState, funT1: FunT1, mapEx: TlaEx, varName: String, setEx: TlaEx) = {
    // rewrite the set expression into a memory cell
    var nextState = rewriter.rewriteUntilDone(state.setRex(setEx))

    val funT = CellT.fromType1(funT1)
    val (elemT, codomain) =
      funT1 match {
        case FunT1(argT, IntT1()) =>
          (CellT.fromType1(argT), ValEx(TlaIntSet))

        case FunT1(argT, BoolT1()) =>
          (CellT.fromType1(argT), ValEx(TlaBoolSet))

        case FunT1(argT, resultT) =>
          val msg = "A result of a recursive function must belong to Int or BOOLEAN. Found: " + resultT
          throw new RewriterException(msg, state.ex)
      }

    // one more safety check, as the domain cell can happen to be a powerset or a function set
    val domainCell = nextState.asCell
    domainCell.cellType match {
      case FinSetT(et) => et
      case t @ _       => throw new RewriterException("Expected a finite set, found: " + t, state.ex)
    }

    // produce a cell for the function set (no expansion happens there)
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.funSet(domainCell.toNameEx, codomain)))
    val funSetCell = nextState.asCell
    // pick a function from the function set
    nextState = pick.pickFunFromFunSet(funT, funSetCell, nextState)
    val funCell = nextState.asCell
    nextState = nextState.setBinding(
        new Binding(nextState.binding.toMap + (TlaFunOper.recFunRef.uniqueName -> funCell)))
    // for every element of the domain, add the constraint imposed by the definition
    val domainCells = nextState.arena.getHas(domainCell)
    for (elem <- domainCells) {
      val oldBinding = nextState.binding
      // compute the right-hand side of the constraint by the recursive function
      nextState = rewriter.rewriteUntilDone(
          nextState
            .setRex(mapEx)
            .setBinding(new Binding(oldBinding.toMap + (varName -> elem))))
      val rhs = nextState.asCell
      // Compute the left-hand side of the constraint, that is, f[elem].
      nextState = nextState.setBinding(oldBinding)
      nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.appFun(funCell.toNameEx, elem.toNameEx)))
      val lhs = nextState.asCell
      // either elem is outside of DOMAIN, or lhs equals rhs
      val pred = tla.or(inOpFactory.mkUnchangedOp(elem, domainCell), tla.eql(lhs.toNameEx, rhs.toNameEx))
      rewriter.solverContext.assertGroundExpr(pred)
    }

    // that's it
    nextState
      .setRex(funCell.toNameEx)
      .setBinding(new Binding(nextState.binding.toMap - TlaFunOper.recFunRef.uniqueName))
  }
}
