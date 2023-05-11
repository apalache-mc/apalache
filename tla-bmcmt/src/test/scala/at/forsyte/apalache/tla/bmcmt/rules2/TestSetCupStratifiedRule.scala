package at.forsyte.apalache.tla.bmcmt.rules2

import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, Binding, FixedElemPtr, PureArena}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSetCupStratifiedRule extends AnyFunSuite {

  sealed case class MockRewriter(cheatyMap: Map[UID, ArenaCell]) extends Rewriter {
    def rewrite(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell) =
      (startingScope, cheatyMap(ex.ID))
  }

  test("Union of two sets with a nonempty intersection. ") {

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

    // We don't have other rules implemented, so we have to hack it a bit
    val cellMap: Map[UID, ArenaCell] = cup match {
      case OperEx(_, left, right) =>
        Map(
            left.ID -> lSetCell,
            right.ID -> rSetCell,
        )
      case _ => Map.empty // impossible, but silences compiler warning
    }
    val rule = new SetCupStratifiedRule(MockRewriter(cellMap))

    val startScope = RewriterScope(arenaWithHas, new Binding(Map.empty))

    val (RewriterScope(resultArena, _), resultCell) = rule.apply(cup)(startScope)

    assert {
      resultArena.getHas(resultCell) == lElems.map(FixedElemPtr)
    }

  }
}
