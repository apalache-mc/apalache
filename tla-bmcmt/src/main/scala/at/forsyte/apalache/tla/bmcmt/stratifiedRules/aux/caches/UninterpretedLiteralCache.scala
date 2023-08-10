package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.{CellT, CellTFrom}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, PureArena}
import at.forsyte.apalache.tla.lir.{ConstT1, StrT1, TlaType1}
import at.forsyte.apalache.tla.types.tla

/**
 * A cache for uninterpreted literals, that are translated as uninterpreted SMT constants, with a unique sort per
 * uninterpreted type. Since two values are equal iff they are literally the same literal, we force inequality between
 * all the respective SMT constants.
 *
 * Note that Strings are just a special kind of uninterpreted type.
 *
 * @author
 *   Jure Kukovec
 */
class UninterpretedLiteralCache extends Cache[PureArena, (TlaType1, String), ArenaCell] {

  /**
   * Given a pair `(utype,idx)`, where `utype` represents an uninterpreted type name (possibly "Str") and `idx` some
   * unique index within that type, returns an extension of `arena`, containing a cell, which represents "idx_OF_utype"
   * (or "idx", if utype = "Str"), and said cell.
   *
   * Note that two values are equal (and get cached to the same cell) iff they have the same type and the same index, so
   * e.g. "1_OF_A" and "1_OF_B" (passed here as ("A", "1") and ("B", "1")) get cached to different, incomparable cells,
   * despite having the same index "1".
   */
  protected def create(
      arena: PureArena,
      typeAndIndex: (TlaType1, String)): (PureArena, ArenaCell) = {
    val (utype, _) = typeAndIndex
    require(utype == StrT1 || utype.isInstanceOf[ConstT1], "Type must be Str, or an uninterpreted type.")
    // introduce a new cell
    val newArena = arena.appendCell(CellT.fromType1(utype))
    (newArena, newArena.topCell)
  }

  /**
   * The UninterpretedLiteralCache maintains that a cell cache for a value `idx` of type `tp` is distinct from all other
   * values of type `tp` (defined so far).
   *
   * Whenever possible, try to use [[addAllConstraints]] instead of this method, for performance reasons instead:
   *
   * If we consider a naive implementation of `distinct(a1,..., an)` as `a1 != a2 /\ a1 != a3 /\ ... /\ a{n-1} != an`, a
   * `distinct` with `n` elements is equivalent to `dn = n(n-1)/2` disequalities. Suppose we end up with a collection of
   * `N` cache values (of a given type). If we called `addConstaintsForElem` after each addition, we'd end up with `d1 +
   * d2 + ... + dN` disequalities, i.e. {{{\sum_{n=1}^N n(n-1)/2 = N(N^2 -1)/6}}} In contrast, `addAllConstraints`
   * produces `dN = N(N-1)/2` disequalities, which is `O(N^2)`, instead of `O(N^3)`.
   */
  override def addConstraintsForElem(ctx: SolverContext): (((TlaType1, String), ArenaCell)) => Unit = {
    case ((utype, _), v) =>
      require(utype == StrT1 || utype.isInstanceOf[ConstT1], "Type must be Str, or an uninterpreted type.")
      val others = values().withFilter { c => c.cellType == CellTFrom(utype) && c != v }.map(_.toBuilder).toSeq
      // The cell should differ from the previously created cells.
      // We use the SMT constraint (distinct ...).
      ctx.assertGroundExpr(tla.distinct(v.toBuilder +: others: _*))
  }

  /**
   * A more efficient implementation, compared to the default one, as it introduces exactly one SMT `distinct` for each
   * uninterpreted type instead of one `distinct` per cell.
   */
  override def addAllConstraints(ctx: SolverContext): Unit = {
    val utypes = cache.keySet.map { _._1 }

    val initMap = utypes.map { _ -> Set.empty[ArenaCell] }.toMap

    val cellsByUtype = cache.foldLeft(initMap) { case (map, ((utype, _), (cell, _))) =>
      map + (utype -> (map(utype) + cell))
    }

    // For each utype, all cells of that type are distinct
    cellsByUtype.foreach { case (_, cells) =>
      ctx.assertGroundExpr(tla.distinct(cells.toSeq.map { _.toBuilder }: _*))
    }

  }
}
