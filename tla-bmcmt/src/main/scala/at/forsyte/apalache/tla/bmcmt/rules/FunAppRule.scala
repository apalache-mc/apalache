package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.{FailPredT, RecordT, TupleT}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

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

            case RecordT(_) =>
              applyRecord(funState, funCell, funEx, argEx)

            case _ =>
              applyFun(funState, funCell, argEx)
          }
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def applyRecord(state: SymbState, recordCell: ArenaCell, funEx: TlaEx, argEx: TlaEx): SymbState = {
    val key = argEx match {
      case ValEx(TlaStr(k)) => k
      case _ => throw new RewriterException(s"Accessing a record $funEx with a non-constant key $argEx")
    }
    val fields = recordCell.cellType match {
      case RecordT(f) => f
      case t @ _ => throw new RewriterException(s"Corrupted record $funEx of a non-record type $t")
    }
    val index = fields.keySet.toList.indexOf(key)
    val tupleCell = state.arena.getHas(recordCell).head
    val elems = state.arena.getHas(tupleCell)
    if (index >= 0 && index < elems.length) {
      val keyCell = rewriter.strValueCache.get(key).get
      // when key is outside the record domain, we do not flag a failure here,
      // since records of different types are often used in TLA+ specifications, e.g., see Paxos.tla
      val tupleElem = elems(index)
      state.setTheory(CellTheory()).setRex(tupleElem)
    } else {
      // FIXME: use the code below as soon as type inference is working correctly
      // Now we are trouble, since we don't know the type of a value we should return.
      // SymbStateRewriter will try to resolve it at upper levels
      val msg = s"Accessing record $funEx of type ${recordCell.cellType} with the key $argEx. Filter the set first?"
      throw new UndefinedBehaviorError(msg, state.arena)
      // This case should have been caught by type inference. Throw an exception.
//      val msg = s"Accessing record $funEx of type ${recordCell.cellType} with the field $argEx. Type inference should have caught this."
//      throw new IllegalArgumentException(msg)
    }
  }

  private def applyTuple(state: SymbState, tupleCell: ArenaCell, funEx: TlaEx, argEx: TlaEx): SymbState = {
    val simpleArg = simplifier.simplify(argEx)
    val index = simpleArg match {
      case ValEx(TlaInt(i)) => i.toInt - 1

      case _ =>
        throw new RewriterException("Accessing a tuple with a non-constant index: " + argEx)
    }

    val elems = state.arena.getHas(tupleCell)
    if (index < 0 || index >= elems.length) {
      throw new RewriterException(s"Out of bounds index ${index + 1} in $funEx[$argEx]")
    }

    val tupleElem = elems(index)
    state.setTheory(CellTheory()).setRex(tupleElem)
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
//    val newArena = resState.arena.appendCell(FailPredT())
//    val failPred = newArena.topCell
//    rewriter.addMessage(failPred.id,
//      "Argument %s may be outside the function %s domain %s".format(argEx, funCell, state.arena.getDom(funCell)))
    // cache equalities
    val eqState = rewriter.lazyEq.cacheEqConstraints(resState,
      domCells.map(e => (e, argCell)))

    // Equation (2): there is a domain element that equals to the argument
    def mkArgCase(domElem: ArenaCell): TlaEx = {
      val inDomain = tla.in(domElem, domainCell)
      val argEq = rewriter.lazyEq.safeEq(domElem, argCell) // just use SMT equality
      tla.and(inDomain, argEq)
    }
    // the result equals to the function result (bugfix: separate mkArgCase from mkResCase)
    def mkResCase(domElem: ArenaCell): TlaEx = {
      val inDomain = tla.in(domElem, domainCell)
      val resEq =
        tla.eql(resultCell, tla.appFun(funCell, domElem)) // translated as function application in SMT
      val argEq = rewriter.lazyEq.safeEq(domElem, argCell) // just use SMT equality
      tla.and(inDomain, argEq, resEq)
    }

    // Equation (3): there is no domain element that equals to the argument
//    def mkNotInCase(domElem: ArenaCell): TlaEx = {
//      val notInDomain = tla.not(tla.in(domElem, domainCell))
//      val eq = rewriter.lazyEq.safeEq(domElem, argCell) // just use SMT equality
//      tla.or(notInDomain, tla.not(eq))
//    }

    val foundFlag = rewriter.solverContext.introBoolConst() // XXX: remove
    val found = tla.or(domCells.map(mkArgCase): _*) //tla.and(tla.not(failPred), tla.or(domCells.map(mkInCase): _*))
    rewriter.solverContext.assertGroundExpr(tla.equiv(tla.name(foundFlag), found))
    val resEq = tla.impl(found, tla.or(domCells.map(mkResCase): _*))
    rewriter.solverContext.assertGroundExpr(resEq)

    var newArena = eqState.arena.appendCell(FailPredT())
    val failPred = newArena.topCell
    rewriter.addMessage(failPred.id,
      "Argument %s may be outside the function %s domain %s".format(argEx, funCell, state.arena.getDom(funCell)))
    rewriter.solverContext.assertGroundExpr(tla.equiv(failPred.toNameEx, tla.not(NameEx(foundFlag))))

    rewriter.rewriteUntilDone(eqState.setArena(newArena).setRex(resultCell).setTheory(CellTheory()))
  }


}
