package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.{ElemPtr, _}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction

/**
 * Implements a rule for Apalache!SetAsFun.
 *
 * @author
 *   Igor Konnov
 */
class SetAsFunRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(ApalacheOper.setAsFun, _) => true
      case _                                => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(ApalacheOper.setAsFun, setEx) =>
        var nextState = rewriter.rewriteUntilDone(state.setRex(setEx))
        val setCell = nextState.asCell
        setEx.typeTag match {
          case Typed(SetT1(TupT1(keyType, valueType))) =>
            // construct a cell for the function and attach the relation to it
            nextState = nextState.updateArena(_.appendCell(FunT1(keyType, valueType)))
            val fun = nextState.arena.topCell

            rewriter.solverContext.config.smtEncoding match {
              case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
                nextState = nextState.updateArena(_.appendCell(SetT1(keyType)))
                val domainCell = nextState.arena.topCell
                nextState = nextState.updateArena(_.appendCellNoSmt(setCell.cellType))
                val relationCell = nextState.arena.topCell

                val pairs = nextState.arena.getHasPtr(setCell)
                var domainCells: List[ArenaCell] = List()
                var rangeCells: List[ArenaCell] = List()

                for (pairPtr <- pairs) {
                  val pair = pairPtr.elem
                  assert(nextState.arena.getHas(pair).length == 2)
                  val Seq(domElemPtr, resElemPtr) = nextState.arena.getHasPtr(pair)
                  val domElem = domElemPtr.elem
                  val resElem = resElemPtr.elem

                  nextState = nextState.updateArena(_.appendHas(domainCell, domElemPtr))
                  val inExpr = tla.storeInSet(domElem.toBuilder, domainCell.toBuilder)
                  rewriter.solverContext.assertGroundExpr(inExpr)

                  nextState = nextState.updateArena(_.appendHasNoSmt(relationCell, pairPtr))

                  domainCells = domainCells :+ domElem
                  rangeCells = rangeCells :+ resElem
                }

                nextState = nextState.updateArena(_.setDom(fun, domainCell))
                nextState = nextState.updateArena(_.setCdm(fun, relationCell))

                def addCellCons(domElem: ArenaCell, rangeElem: ArenaCell): Unit = {
                  val inDomain = tla.selectInSet(domElem.toBuilder, domainCell.toBuilder)
                  val inRange =
                    tla.storeInSet(rangeElem.toBuilder, fun.toBuilder, domElem.toBuilder)
                  val notInRange = tla.storeNotInFun(domElem.toBuilder, fun.toBuilder)
                  // function updates are guarded by the inDomain predicate
                  val ite = tla.ite(inDomain, inRange, notInRange)
                  rewriter.solverContext.assertGroundExpr(ite)
                }

                // Here we iterate over the reverse order of the list to have, in case duplicate keys, the first entry
                // in the list be the value encoded in the function. This is the semantics of SMTEncoding.OOPSLA19.
                for ((domElem, rangeElem) <- domainCells.zip(rangeCells).reverse)
                  addCellCons(domElem, rangeElem)

              case SMTEncoding.OOPSLA19 =>
                nextState = translateRelation(setCell, nextState)
                val rel = nextState.asCell
                nextState = nextState.updateArena(_.setCdm(fun, rel))

              case oddEncodingType =>
                throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
            }

            nextState.setRex(fun.toBuilder)

          case tt =>
            throw new RewriterException("Unexpected type in SetAsFunRule: " + tt, state.ex)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  /**
   * <p>Translate a set of pairs `{ <<key_1, value_1>>, ..., <<key_n, value_n>> }` to a function that is equivalent
   * to:</p>
   *
   * <pre>
   *
   * x \in { key_1, ..., key_n } |-> IF x = key_1 THEN value_1 ELSE IF x = key_2 THEN value_2 ELSE ... value_n ] </pre>
   */
  private def translateRelation(pairsSet: ArenaCell, state: SymbState): SymbState = {
    var nextState = state.updateArena(_.appendCellOld(pairsSet.cellType))
    // construct the relation cell `funRel` and add all cells from the original set `setCell`
    val funRel = nextState.arena.topCell
    val pairs = nextState.arena.getHasPtr(pairsSet)
    nextState = nextState.updateArena(_.appendHas(funRel, pairs: _*))
    // however, iteratively restrict the membership, to enforce determinism
    for ((pair1Ptr, idx1) <- pairs.zipWithIndex) {
      val pair1 = pair1Ptr.elem
      val key1 = nextState.arena.getHas(pair1).head

      // ensure that a pair with the same key has not been included in the relation yet
      def keysDifferOrNotIncluded(pair2Ptr: ElemPtr): TBuilderInstruction = {
        val pair2 = pair2Ptr.elem
        val key2 = nextState.arena.getHas(pair2).head
        // pair2 \notin funRel
        val notInFunRel = tla.not(tla.selectInSet(pair2.toBuilder, funRel.toBuilder))
        // key1 = key2
        nextState = rewriter.lazyEq.cacheOneEqConstraint(nextState, key1, key2)
        val keysEq = tla.unchecked(rewriter.lazyEq.cachedEq(key1, key2))
        // pair2 \notin funRel \/ key1 /= key2
        tla.or(notInFunRel, tla.not(keysEq))
      }

      val noDuplicateKeys = tla.and(pairs.slice(0, idx1).map(keysDifferOrNotIncluded): _*)
      // pair1 \in setCell
      val inSet = tla.selectInSet(pair1.toBuilder, pairsSet.toBuilder)
      // pair1 \in funRel <=> pair1 \in setCell /\ notInPrefix
      val ite = tla.ite(tla.and(inSet, noDuplicateKeys), tla.storeInSet(pair1.toBuilder, funRel.toBuilder),
          tla.storeNotInSet(pair1.toBuilder, funRel.toBuilder))
      rewriter.solverContext.assertGroundExpr(ite)
    }

    nextState.setRex(funRel.toBuilder)
  }
}
