package at.forsyte.apalache.tla.bmcmt.rules.support

import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types.{CellTFrom, FinFunSetT, InfSetT, PowSetT}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, SymbState}
import at.forsyte.apalache.tla.lir.SetT1
import at.forsyte.apalache.tla.types.{BuilderUT => BuilderT, tlaU => tla}

/**
 * A predicate that holds exactly when the set is empty. When the membership can be predicted statically, the predicate
 * is `tla.bool(true)` or `tla.bool(false)`.
 */
sealed trait SetEmptiness {
  def predicate: BuilderT
}

object SetEmptiness {
  case object StaticallyEmpty extends SetEmptiness {
    override val predicate: BuilderT = tla.bool(true)
  }

  case object StaticallyNonEmpty extends SetEmptiness {
    override val predicate: BuilderT = tla.bool(false)
  }

  case class SymbolicallyEmptyWhen(predicate: BuilderT) extends SetEmptiness

  private val simplifier = new ConstSimplifierForSmt

  private def simplify(ex: BuilderT): BuilderT = simplifier.applySimplifyShallowToBuilderEx(ex)

  /**
   * Classify set emptiness from its rewritten arena representation, without expanding lazy sets. Arena edges represent
   * potential membership, so having edges does not in general imply that the set is nonempty.
   */
  def apply(state: SymbState, set: ArenaCell): SetEmptiness = {
    set.cellType match {
      case CellTFrom(SetT1(_)) =>
        val pointersAndPredicates = state.arena.getHasPtr(set).map(ptr => ptr -> simplify(ptr.toSmt))
        if (pointersAndPredicates.exists { case (_, pred) => simplifier.isTrueConst(pred) }) {
          StaticallyNonEmpty
        } else {
          // Remove the elements that are known to be non-members statically.
          val potentialMembers =
            pointersAndPredicates.filterNot { case (_, pred) => simplifier.isFalseConst(pred) }.map(_._1.elem)
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
        val domEmptiness = apply(state, state.arena.getDom(set))
        val cdmEmptiness = apply(state, state.arena.getCdm(set))
        isFunSetEmpty(domEmptiness, cdmEmptiness)

      case unexpected =>
        throw new RewriterException(s"Expected a set cell, found: $unexpected", state.ex)
    }
  }

  private def isFunSetEmpty(dom: SetEmptiness, cdm: SetEmptiness): SetEmptiness = {
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
}
