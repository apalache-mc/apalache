package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
  * Implements the rules: SE-LOG-EX[1-3] and SE-LOG-ALL[1-3].
  *
  * @author Igor Konnov
  */
class QuantRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pickRule = new PickFromAndFunMerge(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.exists, _, _, _) => true
      case OperEx(TlaBoolOper.forall, _, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaBoolOper.exists, NameEx(boundVar), boundingSetEx, predEx) =>
        rewriteExistsOrForall(isExists = true, state, boundVar, boundingSetEx, predEx)

      case OperEx(TlaBoolOper.forall, NameEx(boundVar), boundingSetEx, predEx) =>
        rewriteExistsOrForall(isExists = false, state, boundVar, boundingSetEx, predEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def rewriteExistsOrForall(isExists: Boolean,
                                    state: SymbState, boundVar: String, boundingSetEx: TlaEx, predEx: TlaEx) = {
    // first, evaluate boundingSet
    val setState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(boundingSetEx))
    val set = setState.arena.findCellByNameEx(setState.ex)
    val setCells = setState.arena.getHas(set)
    val finalState =
      if (setCells.isEmpty) {
        // 'exists' over an empty set always returns false, while 'forall' returns true
        val constResult =
          if (isExists)
            setState.solverCtx.falseConst
          else
            setState.solverCtx.trueConst

        setState.setTheory(BoolTheory()).setRex(NameEx(constResult))
      } else {
        def mkPair(elemCell: ArenaCell): (Binding, TlaEx) = {
          val newBinding = setState.binding + (boundVar -> elemCell)
          (newBinding, predEx)
        }

        // rewrite p[c_i/x] for every c_i \in boundingSet
        val (predState: SymbState, predEs: Seq[TlaEx]) =
          rewriter.rewriteBoundSeqUntilDone(setState.setTheory(BoolTheory()), setCells.map(mkPair))

        val nonEmpty = tla.or(setCells.map(tla.in(_, set)): _*)
        val empty = tla.and(setCells.map(c => tla.not(tla.in(c, set))): _*)

        def elemWitnesses(elemAndPred: (ArenaCell, TlaEx)): TlaEx = {
          tla.and(tla.in(elemAndPred._1, set), elemAndPred._2)
        }
        def elemSatisfies(elemAndPred: (ArenaCell, TlaEx)): TlaEx = {
          tla.or(tla.not(tla.in(elemAndPred._1, set)), elemAndPred._2)
        }

        val pred = NameEx(predState.solverCtx.introBoolConst())
        val iff =
          if (isExists) {
            // \E x \in S: p holds iff nonEmpty /\ \/_i (p[c_i/x] /\ c_i \in set)
            val existsElem = tla.or(setCells.zip(predEs).map(elemWitnesses): _*)
            tla.equiv(pred, tla.and(nonEmpty, existsElem))
          } else {
            // \A x \in S: p holds iff empty \/ /\_i (~p[c_i/x] \/ ~c_i \in set)
            val allElem = tla.and(setCells.zip(predEs).map(elemSatisfies): _*)
            tla.equiv(pred, tla.or(empty, allElem))
          }
        predState.solverCtx.assertGroundExpr(iff)

        predState.setRex(pred)
          .setTheory(BoolTheory())
          .setBinding(predState.binding - boundVar) // forget the binding to x, but not the other bindings!
      }

    rewriter.coerce(finalState, state.theory)
  }

  // this is a special form of exists, which we will use later
  private def specialExists(setState: SymbState, boundVar: String, predEx: TlaEx, set: ArenaCell, setCells: List[ArenaCell]) = {
    // pick an arbitrary witness
    val pickState = pickRule.pick(set, setState)
    val pickedCell = pickState.arena.findCellByNameEx(pickState.ex)
    // enforce that the witness satisfies the predicate
    val extendedBinding = pickState.binding + (boundVar -> pickedCell)
    // predState.ex contains the predicate applied to the witness
    val predState = rewriter.rewriteUntilDone(pickState
      .setTheory(BoolTheory()).setRex(predEx).setBinding(extendedBinding))
    val predWitness = predState.ex

    // \E x \in S: p holds iff predWitness /\ S /= {}
    val exPred = NameEx(predState.solverCtx.introBoolConst())
    val notEmpty = tla.or(setCells.map(e => tla.in(e, set)): _*)
    val iff = tla.equiv(exPred, tla.and(predWitness, notEmpty))
    predState.solverCtx.assertGroundExpr(iff)

    predState.setRex(exPred)
      .setTheory(BoolTheory())
      .setBinding(predState.binding - boundVar) // forget the binding to x, but not the other bindings!
  }
}