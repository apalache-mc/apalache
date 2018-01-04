package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.{FailPredT, TupleT}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, ValEx}

/**
  * Implements the rules: SE-FUN-APP[1-3].
  *
  * @author Igor Konnov
  */
class FunAppRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val picker = new PickFromAndFunMerge(rewriter)
  private val simplifier = new ConstSimplifier()

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.app, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.app, funEx, argEx) =>
        // SE-FUN-APP1
        val funState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(funEx))
        val funCell = funState.arena.findCellByNameEx(funState.ex)

        val finalState =
          funCell.cellType match {
            case TupleT(_) =>
              applyTuple(funState, funCell, funEx, argEx)

            case _ =>
              applyFun(funState, funCell, argEx)
          }
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def applyTuple(state: SymbState, tupleCell: ArenaCell, funEx: TlaEx, argEx: TlaEx): SymbState = {
    val simpleArg = simplifier.simplify(argEx)
    simpleArg match {
      case ValEx(TlaInt(i)) =>
        val elems = state.arena.getHas(tupleCell)
        val index = i.toInt - 1
        if (index < 0 || index >= elems.length) {
          throw new RewriterException(s"Out of bounds index ${index + 1} in $funEx[$argEx]")
        }

        val tupleElem = elems(index)
        state.setTheory(CellTheory()).setRex(tupleElem)

      case _ =>
        throw new RewriterException("Accessing a tuple with a non-constant index: " + argEx)
    }
  }

  private def applyFun(state: SymbState, funCell: ArenaCell, argEx: TlaEx): SymbState = {
    // SE-FUN-APP2
    val argState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(argEx))
    val argCell = argState.arena.findCellByNameEx(argState.ex)

    val domainCell = argState.arena.getDom(funCell)
    val codomainCell = argState.arena.getCdm(funCell)
    val resState = picker.pick(codomainCell, argState)

    // SE-FUN-APP3
    val resultCell = resState.ex
    val domCells = resState.arena.getHas(domainCell)

    // introduce a new failure predicate
    val newArena = resState.arena.appendCell(FailPredT())
    val failPred = newArena.topCell
    // cache equalities
    val eqState = rewriter.lazyEq.cacheEqConstraints(resState.setArena(newArena),
      domCells.map(e => (e, argCell)))

    // Equation (2): there is a domain element that equals to the argument
    def mkInCase(domElem: ArenaCell): TlaEx = {
      val inDomain = tla.in(domElem, domainCell)
      val funEqResult =
        tla.eql(resultCell, tla.appFun(funCell, domElem)) // translated as function application in SMT
      val eq = rewriter.lazyEq.safeEq(domElem, argCell) // just use SMT equality
      tla.and(inDomain, eq, funEqResult)
    }

    // Equation (3): there is no domain element that equals to the argument
    def mkNotInCase(domElem: ArenaCell): TlaEx = {
      val notInDomain = tla.not(tla.in(domElem, domainCell))
      val eq = rewriter.lazyEq.safeEq(domElem, argCell) // just use SMT equality
      tla.or(notInDomain, tla.not(eq))
    }

    val found = tla.and(tla.not(failPred), tla.or(domCells.map(mkInCase): _*))
    val notFound = tla.and(failPred, tla.and(domCells.map(mkNotInCase): _*))
    rewriter.solverContext.assertGroundExpr(tla.or(found, notFound))

    eqState.setRex(resultCell).setTheory(CellTheory())
  }
}
