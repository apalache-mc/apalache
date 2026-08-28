package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types.{CellTFrom, FinFunSetT, InfSetT, PowSetT}
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.{BuilderUT => BuilderT, tlaU => tla}

/**
 * This rule constructs a cell for a function set [S -> T]. Nontrivial function sets stay unexpanded and point to S
 * and T. Function sets with a definitely empty operand are represented as an ordinary empty or singleton set.
 *
 * @author
 *   Igor Konnov
 */
class FunSetCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val simplifier = new ConstSimplifierForSmt

  /**
   * Set emptiness classification.
   */
  sealed private trait SetEmptiness {
    /**
     * The set is empty when the predicate holds true.
     */
    def predicate: BuilderT
  }

  /**
   * A set is empty at translation time.
   */
  private case object StaticallyEmpty extends SetEmptiness {
    override val predicate: BuilderT = tla.bool(true)
  }

  /**
   * A set is non-empty at translation time.
   */
  private case object StaticallyNonEmpty extends SetEmptiness {
    override val predicate: BuilderT = tla.bool(false)
  }

  /**
   * A set may be empty when the predicate evaluates to true (in SMT).
   */
  private case class SymbolicallyEmptyWhen(predicate: BuilderT) extends SetEmptiness

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.funSet, _, _) => true
      case _                               => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case funSetEx@OperEx(TlaSetOper.funSet, domEx, cdmEx) =>
        // switch to cell theory
        var nextState = rewriter.rewriteUntilDone(state.setRex(domEx))
        val dom = nextState.asCell
        nextState = rewriter.rewriteUntilDone(nextState.setRex(cdmEx))
        val cdm = nextState.asCell

        val funT = TlaType1.fromTypeTag(funSetEx.typeTag) match {
          case SetT1(ft@FunT1(_, _)) => ft
          case t =>
            throw new TypingException(s"Function-set $funSetEx should have a set-of-functions type, found: $t",
              funSetEx.ID)
        }

        (setEmptiness(nextState, dom), setEmptiness(nextState, cdm)) match {
          // There is exactly one function over the empty domain, independently of the co-domain.
          case (StaticallyEmpty, _) =>
            makeSingletonWhen(nextState, funT, tla.bool(true))

            // [S -> {}] contains the empty function exactly when S is empty.
          case (domEmptiness, StaticallyEmpty) =>
            makeSingletonWhen(nextState, funT, domEmptiness.predicate)

            // the default case: rewrite to a special cell without expanding the set of functions
          case _ =>
            val arena = nextState.arena.appendCellOld(FinFunSetT(dom.cellType, cdm.cellType))
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

  /**
   * Classify set emptiness from its rewritten arena representation. In particular, an ordinary finite set is empty when
   * all of its potential membership pointers are false. The symbolic predicate is retained when emptiness depends on
   * the current model.
   */
  private def setEmptiness(state: SymbState, set: ArenaCell): SetEmptiness = {
    def simplify(ex: BuilderT): BuilderT = simplifier.applySimplifyShallowToBuilderEx(ex)

    set.cellType match {
      case CellTFrom(SetT1(_)) =>
        val pointersAndPredicates = state.arena.getHasPtr(set).map(ptr => ptr -> simplify(ptr.toSmt))
        if (pointersAndPredicates.exists { case (_, pred) => simplifier.isTrueConst(pred) }) {
          StaticallyNonEmpty
        } else {
          // remove the elements that are known to be non-members statically
          val potentialMembers = pointersAndPredicates.filterNot { case (_, pred) => simplifier.isFalseConst(pred) }.map(_._1.elem)
          if (potentialMembers.isEmpty) {
            StaticallyEmpty
          } else {
            // Pointer conditions are arena metadata and, in the Arrays encoding, may contain store expressions.
            // Use actual set membership for the semantic emptiness predicate.
            val noMember = potentialMembers.map(elem => tla.not(tla.selectInSet(elem.toBuilder, set.toBuilder)))
            SymbolicallyEmptyWhen(simplify(tla.and(noMember: _*)))
          }
        }

        // Every powerset contains the empty set. The built-in infinite sets are non-empty too.
      case PowSetT(_) | InfSetT(_) =>
        StaticallyNonEmpty

        // [S -> T] is empty exactly when S is non-empty and T is empty.
      case FinFunSetT(_, _) =>
        val domEmptiness = setEmptiness(state, state.arena.getDom(set))
        val cdmEmptiness = setEmptiness(state, state.arena.getCdm(set))
        isFunSetEmpty(domEmptiness, cdmEmptiness)

      case unexpected =>
        throw new RewriterException(s"Expected a set cell, found: $unexpected", state.ex)
    }
  }

  private def isFunSetEmpty(dom: SetEmptiness, cdm: SetEmptiness): SetEmptiness = {
    def simplify(ex: BuilderT): BuilderT = simplifier.applySimplifyShallowToBuilderEx(ex)

    (dom, cdm) match {
      case (StaticallyEmpty, _) | (_, StaticallyNonEmpty) =>
        StaticallyNonEmpty
      case (StaticallyNonEmpty, StaticallyEmpty) =>
        StaticallyEmpty
      case (StaticallyNonEmpty, SymbolicallyEmptyWhen(cdmPred)) =>
        SymbolicallyEmptyWhen(cdmPred)
      case (SymbolicallyEmptyWhen(domPred), StaticallyEmpty) =>
        SymbolicallyEmptyWhen(simplify(tla.not(domPred)))
      case (SymbolicallyEmptyWhen(domPred), SymbolicallyEmptyWhen(cdmPred)) =>
        SymbolicallyEmptyWhen(simplify(tla.and(tla.not(domPred), cdmPred)))
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
