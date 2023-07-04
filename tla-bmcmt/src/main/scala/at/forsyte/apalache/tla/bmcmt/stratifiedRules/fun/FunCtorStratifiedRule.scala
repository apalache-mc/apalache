package at.forsyte.apalache.tla.bmcmt.stratifiedRules.fun

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.{Rewriter, RewriterScope}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.{addCell, StratifiedRule}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.types.tla

/**
 * The new implementation of a function constructor that encodes a function f = [x \in S |-> e] the classical way: f =
 * {(a, b) : a \in S, b = e[a/x]}. For efficiency, we are still carrying the domain set in a separate cell.
 *
 * @author
 *   Jure Kukovec
 */
class FunCtorStratifiedRule(rewriter: Rewriter) extends StratifiedRule[ArenaCell] {

  def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = ex match {
    case OperEx(TlaFunOper.funDef, _*) => true
    case _                             => false
  }

  def buildArena(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell, ArenaCell) = ex match {
    case ex @ OperEx(TlaFunOper.funDef, mapEx, name @ NameEx(varName), setEx) =>
      val funT = TlaType1.fromTypeTag(ex.typeTag).asInstanceOf[FunT1]
      // rewrite the set expression into a memory cell
      val (afterSetScope, domainCell) = rewriter.rewrite(setEx)(startingScope)
      val domainCellPtrs = afterSetScope.arena.getHas(domainCell)
      // find the type of the target expression and of the target set
      // unfold the set and map every potential element to a cell
      // actually, instead of mapping every cell to e, we map it to <<x, e>> to construct the relation
      val pairEx = tla.tuple(tla.unchecked(name), tla.unchecked(mapEx))

      def mapOne(cellPtr: ElemPtr): ElemPtr = {
        // rewrite mapEx[cell/varName]
        val newBinding = Binding(afterSetScope.binding.toMap + (varName -> cellPtr.elem))
        // Note: we forget about arena changes below this rewrite after exiting this function
        // Make sure (with tests) that this is correct!
        val (_, cell) = rewriter.rewrite(pairEx)(afterSetScope.copy(binding = newBinding))
        cellPtr match {
          case _: FixedElemPtr => FixedElemPtr(cell)
          case _               => SmtExprElemPtr(cell, cellPtr.toSmt)
        }
      }

      // compute mappings for all the cells (some of them may coincide, that's fine)
      val relationCellPtrs = domainCellPtrs.map(mapOne)

      // Add the cell for the set that stores the relation <<x, f[x]>>

      val (arenaWithFunCell, funCell) = addCell(afterSetScope.arena, funT)
      val (arenaWithRelation, relation) = addCell(arenaWithFunCell, SetT1(TupT1(funT.arg, funT.res)))
      // For historical reasons, we are using cdm to store the relation, though it is not the co-domain.
      val newArena = arenaWithRelation.appendHas(relation, relationCellPtrs: _*).setCdm(funCell, relation)
      (afterSetScope.copy(arena = newArena), funCell, domainCell)

    case _ =>
      throw new RewriterException("%s is not applicable to %s".format(getClass.getSimpleName, ex), ex)
  }

  def addConstraints(scope: RewriterScope, cell: ArenaCell, auxData: ArenaCell): Unit = {

    val arena = scope.arena
    val domainCell = auxData
    val relation = arena.getCdm(cell)
    val domainCellPtrs = arena.getHas(domainCell)
    val relationCellPtrs = arena.getHas(relation)

    def addCellCons(domElem: ArenaCell, relElem: ArenaCell): Unit = {
      val inDomain = tla.selectInSet(domElem.toBuilder, domainCell.toBuilder)
      val inRelation = tla.storeInSet(relElem.toBuilder, relation.toBuilder)
      val expr = tla.equiv(inDomain, inRelation)

      rewriter.assert(expr)
    }

    // add SMT constraints
    for ((domElemPtr, relElemPtr) <- domainCellPtrs.zip(relationCellPtrs))
      addCellCons(domElemPtr.elem, relElemPtr.elem)
  }
}
