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

  test("Cup") {

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
}
