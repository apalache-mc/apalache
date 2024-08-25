package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.SetT1
import at.forsyte.apalache.tla.types.{tlaU => tla}
import com.typesafe.scalalogging.LazyLogging

/**
 * This class constructs the power set of S, that is, SUBSET S. Sometimes, this is just unavoidable, e.g., consider { Q
 * \in SUBSET S: 2 * Cardinality(Q) = }. Obviously, this produces an enormous explosion of constraints.
 *
 * @author
 *   Igor Konnov
 */
class PowSetCtor(rewriter: SymbStateRewriter) extends LazyLogging {

  // Confringo is the explosion curse from Harry Potter. To let you know that your SMT solver will probably explode.
  def confringo(state: SymbState, set: ArenaCell): SymbState = {
    val elems = state.arena.getHasPtr(set) // S has n elements
    var arena = state.arena // we change the arena a lot
    // Enumerate the bit vectors of length 1..n and construct a set for each vector.
    // Since we do not know statically, which cells belong to S, this method may construct equal sets,
    // which only differ in the elements that do not belong to S.
    // However, in practice, SUBSET S is usually used on S that contains exactly all the cells.
    def mkSetByNum(bitvec: BigInt): ArenaCell = {
      def isIn(no: Int): Boolean = ((bitvec >> no) & 1) != 0
      val filtered = elems.zipWithIndex.filter(p => isIn(p._2)).map(_._1)
      arena = arena.appendCellOld(set.cellType)
      val subsetCell = arena.topCell
      arena = arena.appendHas(subsetCell, filtered: _*)
      for (e <- filtered) {
        val elem = e.elem
        val inSubset = tla.storeInSet(elem.toBuilder, subsetCell.toBuilder)
        val notInSubset =
          tla.storeNotInSet(elem.toBuilder, subsetCell.toBuilder) // This ensures that e is not in subsetCell
        val inSet = tla.selectInSet(elem.toBuilder, set.toBuilder)
        rewriter.solverContext.assertGroundExpr(tla.ite(inSet, inSubset, notInSubset))
      }
      subsetCell
    }

    rewriter.solverContext.log("; %s(%s) {".format(getClass.getSimpleName, state.ex))
    val powSetSize = BigInt(1) << elems.size
    if (powSetSize > Limits.POWSET_MAX_SIZE) {
      logger.error("This error typically occurs when one enumerates all subsets:"
        + " \\A S \\in SUBSET T: P or \\E S \\in SUBSET T: P")
      logger.error("Try to decrease the cardinality of the base set T, or avoid enumeration.")
      val msg =
        s"Attempted to expand SUBSET of size 2^${elems.size}, whereas the built-in limit is ${Limits.POWSET_MAX_SIZE}"
      throw new RewriterKnownLimitationError(msg, state.ex)
    }
    val subsets =
      if (elems.nonEmpty) {
        BigInt(0).to(powSetSize - 1).map(mkSetByNum)
      } else {
        // the set is statically empty: just introduce an empty set
        arena = arena.appendCellOld(set.cellType)
        Seq(arena.topCell)
      }

    // create a cell for the powerset, yeah, it is crazy, but hopefully these subsets are small
    arena = arena.appendCell(SetT1(set.cellType.toTlaType1))
    val powsetCell = arena.topCell
    arena = arena.appendHas(powsetCell, subsets.map(FixedElemPtr): _*)
    for (subset <- subsets) {
      rewriter.solverContext.assertGroundExpr(tla.storeInSet(subset.toBuilder, powsetCell.toBuilder))
    }

    // that's it!
    rewriter.solverContext.log("; } %s returns %s [%d arena cells])"
          .format(getClass.getSimpleName, state.ex, state.arena.cellCount))

    state.setArena(arena).setRex(powsetCell.toNameEx)
  }
}
