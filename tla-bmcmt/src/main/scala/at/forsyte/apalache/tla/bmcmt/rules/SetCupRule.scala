package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.{ElemPtr, FixedElemPtr, SmtExprElemPtr}
import at.forsyte.apalache.tla.lir.{OperEx, TlaType1}
import at.forsyte.apalache.tla.types.tla
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaSetOper}

/**
 * Rewrites X \cup Y, that is, a union of two sets (not UNION). In the first encoding, we used a linear number of `in`
 * queries. However, this happens to be unsound, and we need a quadratic number of queries.
 *
 * @author
 *   Igor Konnov
 */
class SetCupRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.cup, _*) => true
      case _                          => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.cup, leftSet, rightSet) =>
        // rewrite the set expressions into memory cells
        var nextState = rewriter.rewriteUntilDone(state.setRex(leftSet))
        val leftSetCell = nextState.asCell
        nextState = rewriter.rewriteUntilDone(nextState.setRex(rightSet))
        val rightSetCell = nextState.asCell
        val leftPtrs = nextState.arena.getHasPtr(leftSetCell)
        val rightPtrs = nextState.arena.getHasPtr(rightSetCell)

        val leftElems = leftPtrs.map(_.elem).toSet
        val rightElems = rightPtrs.map(_.elem).toSet
        val common = leftElems.intersect(rightElems)

        val cellMap = (leftPtrs ++ rightPtrs).foldLeft(Map.empty[ArenaCell, Seq[ElemPtr]]) { case (m, ptr) =>
          val elem = ptr.elem
          m + (elem -> (m.getOrElse(elem, Seq.empty) :+ ptr))
        }

        // Fixed pointers dominate, if no pointer is fixed we take the disjunction of the smt constraints
        val unionElemPtrs: Seq[ElemPtr] = cellMap.toSeq.map { case (cell, ptrs) =>
          ptrs match {
            case Seq(single) => single
            case _ =>
              if (ptrs.exists { _.isInstanceOf[FixedElemPtr] }) FixedElemPtr(cell)
              else SmtExprElemPtr(cell, tla.or(ptrs.map(_.toSmt): _*))
          }
        }

        rewriter.solverContext.config.smtEncoding match {
          case SMTEncoding.Arrays =>
            // introduce a new set, encoded as a unconstrained array
            val newType = TlaType1.fromTypeTag(state.ex.typeTag)
            nextState = nextState.updateArena(_.appendCell(newType, isUnconstrained = true))
            val newSetCell = nextState.arena.topCell
            nextState = nextState.updateArena(_.appendHas(newSetCell, unionElemPtrs: _*))

            // since newSet is initially unconstrained, we equate it to leftSet to add leftSet's elements to newSet
            rewriter.solverContext.assertGroundExpr(tla.eql(newSetCell.toBuilder, leftSetCell.toBuilder))
            // having added the elements of leftSet to newSet, we use SMT map to add rightSet's elements to newSet
            // we ensure that \forall e \in dom(newSet) : e \in newSet \iff e \in leftSet \lor e \in rightSet
            val smtMap = tla.smtMap(TlaBoolOper.or, rightSetCell.toBuilder, newSetCell.toBuilder)
            rewriter.solverContext.assertGroundExpr(smtMap)

            // that's it
            nextState.setRex(newSetCell.toBuilder)

          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            // introduce a new set
            val newType = TlaType1.fromTypeTag(state.ex.typeTag)
            nextState = nextState.updateArena(_.appendCell(newType))
            val newSetCell = nextState.arena.topCell
            nextState = nextState.updateArena(_.appendHas(newSetCell, unionElemPtrs: _*))

            unionElemPtrs.foreach { ptr =>
              val elem = ptr.elem
              val inL = tla.in(elem.toBuilder, leftSetCell.toBuilder)
              val inR = tla.in(elem.toBuilder, rightSetCell.toBuilder)

              // TODO: replace ITE condition with ptr.toSmt ?
              val cond = {
                if (common.contains(elem)) tla.or(inL, inR)
                else if (leftElems.contains(elem)) inL
                else inR
              }

              val inCup = tla.in(elem.toBuilder, newSetCell.toBuilder)
              val notInCup = tla.notin(elem.toBuilder, newSetCell.toBuilder)
              rewriter.solverContext.assertGroundExpr(tla.ite(cond, inCup, notInCup))
            }

            // that's it
            nextState.setRex(newSetCell.toBuilder)

          case oddEncodingType =>
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
