package at.forsyte.apalache.tla.bmcmt.stratifiedRules

import at.forsyte.apalache.tla.bmcmt.stratifiedRules.set.SetCupStratifiedRule
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, Binding, FixedElemPtr, PureArena}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class SetRewriterTest extends AnyFunSuite with BeforeAndAfterEach {

  var rewriter: TestingRewriter = TestingRewriter(Map.empty)

  override def beforeEach(): Unit = {
    rewriter = TestingRewriter(Map.empty)
  }

  test("Set operator rewriting rule: S \\cup T") {

    val lSetCell = new ArenaCell(0, CellT.fromType1(SetT1(IntT1)))
    val lElems = Seq(1, 2).map(new ArenaCell(_, CellT.fromType1(IntT1)))
    val rSetCell = new ArenaCell(3, CellT.fromType1(SetT1(IntT1)))
    val rElems = Seq(1).map(new ArenaCell(_, CellT.fromType1(IntT1))) // intentional duplicate

    val arena = PureArena.empty.appendCell(lSetCell).appendCellSeq(lElems: _*).appendCell(rSetCell)
    val arenaWithHas =
      arena.appendHas(lSetCell, lElems.map(FixedElemPtr): _*).appendHas(rSetCell, rElems.map(FixedElemPtr): _*)

    val lSet = tla.name("S", SetT1(IntT1))
    val rSet = tla.name("T", SetT1(IntT1))
    val cup = tla.cup(lSet, rSet).build

    val binding = new Binding(Map("S" -> lSetCell, "T" -> rSetCell))

    val rule = new SetCupStratifiedRule(TestingRewriter(Map.empty))

    val startScope = RewriterScope(arenaWithHas, binding)

    val (RewriterScope(resultArena, _), resultCell) = rule.apply(cup)(startScope)

    assert {
      resultArena.getHas(resultCell) == lElems.map(FixedElemPtr)
    }
  }

  test("Set operator rewriting rule: {e1, ..., en}") {

    // Sub-case 1: primitive data
    val cells @ Seq(a, b, c, d) = 0.to(3).map(new ArenaCell(_, CellT.fromType1(IntT1)))

    val binding = Binding(Map(
            "a" -> a,
            "b" -> b,
            "c" -> c,
            "d" -> d,
        ))

    val arena1 = PureArena.empty.appendCellSeq(cells: _*)

    val exEmpty = tla.emptySet(IntT1)

    val exA = tla.name("a", IntT1)
    val exB = tla.name("b", IntT1)
    val exC = tla.name("c", IntT1)
    val exD = tla.name("d", IntT1)

    val exABCD = tla.enumSet(exA, exB, exC, exD)

    val startScope1 = RewriterScope(arena1, binding)

    val (endScope1empty, cellEmptySet) = rewriter.rewrite(exEmpty)(startScope1)

    assert(endScope1empty.arena.getHas(cellEmptySet).isEmpty)

    val (endScope1nonempty, cellNonEmptySet) = rewriter.rewrite(exABCD)(startScope1)

    val endHas = endScope1nonempty.arena.getHas(cellNonEmptySet)

    assert(endHas.size == cells.size && cells.forall(c => endHas.contains(FixedElemPtr(c))))

    // Sub-case 1: Complex data (sets)

    val lSetCell = new ArenaCell(4, CellT.fromType1(SetT1(IntT1)))
    val lElems = Seq(a, b, c)
    val rSetCell = new ArenaCell(5, CellT.fromType1(SetT1(IntT1)))
    val rElems = Seq(d)
    val emptySetCell = new ArenaCell(6, CellT.fromType1(SetT1(IntT1)))

    val arena2 = PureArena.empty.appendCellSeq(cells :+ lSetCell :+ rSetCell :+ emptySetCell: _*)
    val arenaWithHas =
      arena2.appendHas(lSetCell, lElems.map(FixedElemPtr): _*).appendHas(rSetCell, rElems.map(FixedElemPtr): _*)

    val exSetOfSets =
      tla.enumSet(lSetCell.toBuilder, rSetCell.toBuilder, emptySetCell.toBuilder)

    // We don't have the rewriting of cell.toBuilder ~~> cell implemented
    val extendedBinding = Binding(
        binding.toMap ++ Map(
            lSetCell.toString -> lSetCell,
            rSetCell.toString -> rSetCell,
            emptySetCell.toString -> emptySetCell,
        )
    )

    val startScope2 = RewriterScope(arenaWithHas, extendedBinding)

    val (endScope2, cellSetOfSets) = rewriter.rewrite(exSetOfSets)(startScope2)

    val endArena = endScope2.arena
    val parentSetHas = endArena.getHas(cellSetOfSets)

    assert(
        parentSetHas.forall {
          case FixedElemPtr(cell) =>
            Seq(lSetCell, rSetCell, emptySetCell).contains(cell) &&
            endArena.getHas(cell) == arenaWithHas.getHas(cell)
          case _ => false
        }
    )
  }

}
