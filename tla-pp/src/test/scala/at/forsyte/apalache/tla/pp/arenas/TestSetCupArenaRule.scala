package at.forsyte.apalache.tla.pp.arenas

import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, FixedElemPtr, PureArena}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.pp.arenas.rules.SetCupArenaRule
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import scalaz.Scalaz._
import scalaz._

@RunWith(classOf[JUnitRunner])
class TestSetCupArenaRule extends AnyFunSuite {

  sealed case class MockRewriter(cheatyMap: Map[UID, ArenaCell]) extends ArenaRewriter {
    override def rewrite(tlaEx: TlaEx): ArenaComputation = cheatyMap(tlaEx.ID).point[ArenaComputationInternalState]
  }

  test("Basic") {

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
    }
    val rule = new SetCupArenaRule(MockRewriter(cellMap))

    val (ArenaComputationContext(resultArena, _, _), resultCell) =
      rule.apply(cup).run(ArenaComputationContext(arenaWithHas, Map.empty, Map.empty))

    println(resultCell)
    println(resultArena)

  }
}
