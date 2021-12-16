package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.bmcmt.types.FinSetT
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.lir.{BuilderEx, ValEx}

/**
 * This class constructs the power set of S, that is, SUBSET S. Sometimes, this is just unavoidable, e.g.,
 * consider { Q \in SUBSET S: 2 * Cardinality(Q) =  }. Obviously, this produces an enormous explosion of constraints.
 *
 * @author Igor Konnov
 */
class PowSetCtor(rewriter: SymbStateRewriter) {

  // Confringo is the explosion curse from Harry Potter. To let you know that your SMT solver will probably explode.
  def confringo(state: SymbState, set: ArenaCell): SymbState = {
    val elems = state.arena.getHas(set) // S has n elements
    var arena = state.arena // we change the arena a lot
    // Enumerate the bit vectors of length 1..n and construct a set for each vector.
    // Since we do not know statically, which cells belong to S, this method may construct equal sets,
    // which only differ in the elements that do not belong to S.
    // However, in practice, SUBSET S is usually used on S that contains exactly all the cells.
    def mkSetByNum(bitvec: BigInt): ArenaCell = {
      def isIn(no: Int): Boolean = ((bitvec >> no) & 1) != 0
      val filtered = elems.zipWithIndex.filter(p => isIn(p._2)).map(_._1)
      arena = arena.appendCell(set.cellType)
      val subsetCell = arena.topCell
      arena = arena.appendHas(subsetCell, filtered: _*)
      if (filtered.nonEmpty) {
        def addCons(elems: Seq[ArenaCell]): BuilderEx = {
          val elem = elems.head
          val inSet = tla.apalacheSelectInSet(elem.toNameEx, set.toNameEx)

          elems.tail match {
            case Seq() => tla.apalacheStoreInSetOneStep(elem.toNameEx, subsetCell.toNameEx, inSet)
            case tail  => tla.apalacheStoreInSetOneStep(elem.toNameEx, addCons(tail), inSet)
          }
        }

        val cons = addCons(filtered)
        rewriter.solverContext.assertGroundExpr(tla.apalacheStoreInSetLastStep(subsetCell.toNameEx, cons))
      }
      subsetCell
    }

    rewriter.solverContext.log("; %s(%s) {".format(getClass.getSimpleName, state.ex))
    val powSetSize = BigInt(1) << elems.size
    if (powSetSize >= Limits.POWSET_MAX_SIZE) {
      throw new RewriterException(s"Attempted to expand a powerset of size 2^${elems.size}", state.ex)
    }
    val subsets =
      if (elems.nonEmpty) {
        BigInt(0).to(powSetSize - 1) map mkSetByNum
      } else {
        // the set is statically empty: just introduce an empty set
        arena = arena.appendCell(set.cellType)
        Seq(arena.topCell)
      }

    // create a cell for the powerset, yeah, it is crazy, but hopefully these subsets are small
    arena = arena.appendCell(FinSetT(set.cellType))
    val powsetCell = arena.topCell
    arena = arena.appendHas(powsetCell, subsets: _*)
    if (subsets.nonEmpty) {
      def addCons(subsets: Seq[ArenaCell]): BuilderEx = {
        val subset = subsets.head

        subsets.tail match {
          case Seq() => tla.apalacheStoreInSetOneStep(subset.toNameEx, powsetCell.toNameEx, ValEx(TlaBool(true)))
          case tail  => tla.apalacheStoreInSetOneStep(subset.toNameEx, addCons(tail), ValEx(TlaBool(true)))
        }
      }

      val cons = addCons(subsets)
      rewriter.solverContext.assertGroundExpr(tla.apalacheStoreInSetLastStep(powsetCell.toNameEx, cons))
    }

    // that's it!
    rewriter.solverContext.log(
        "; } %s returns %s [%d arena cells])"
          .format(getClass.getSimpleName, state.ex, state.arena.cellCount))

    state.setArena(arena).setRex(powsetCell.toNameEx)
  }
}
