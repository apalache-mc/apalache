package at.forsyte.apalache.tla.bmcmt.stratifiedRules

import at.forsyte.apalache.tla.bmcmt.stratifiedRules.apalache.AssignmentStratifiedRule
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, Binding, PureArena}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class ApalacheRewriterTest extends AnyFunSuite with BeforeAndAfterEach {

  var rewriter: TestingRewriter = TestingRewriter(Map.empty)

  override def beforeEach(): Unit = {
    rewriter = TestingRewriter(Map.empty)
  }

  test("Apalache operator rewriting rule: x := y") {

    val cellName = tla.name("$C$9", IntT1)
    val nonCellStr = "C9"
    val nonCellName = tla.name(nonCellStr, IntT1)

    val rule = new AssignmentStratifiedRule(rewriter)

    def assignTo(lhs: TBuilderInstruction, rhs: TBuilderInstruction = tla.int(1)): TBuilderInstruction =
      tla.assign(tla.prime(lhs), rhs)

    val startScope = RewriterScope.initial()

    assert(!rule.isApplicable(assignTo(cellName), startScope))
    assert(rule.isApplicable(assignTo(nonCellName), startScope))
    assert(!rule.isApplicable(assignTo(nonCellName),
            startScope.copy(binding = Binding(Map(s"$nonCellStr'" -> PureArena.cellInvalid)))))

    val (Seq(xCell, yCell), arena) = Seq(IntT1, IntT1).foldLeft((Seq.empty[ArenaCell], PureArena.initial)) {
      case ((seq, partialArena), cellT) =>
        val (newArena, newCell) = addCell(partialArena, cellT)
        (seq :+ newCell, newArena)
    }

    val scopeWithXY = RewriterScope(arena, new Binding(Map("x" -> xCell, "y" -> yCell)))

    val asgnX = assignTo(nonCellName, tla.name("x", IntT1))
    val asgnY = assignTo(nonCellName, tla.name("y", IntT1))

    val (RewriterScope(_, postBinding1), _) = rewriter.rewrite(asgnX)(scopeWithXY)

    assert(postBinding1.toMap(s"$nonCellStr'") == xCell)

    val (RewriterScope(_, postBinding2), _) = rewriter.rewrite(asgnY)(scopeWithXY)

    assert(postBinding2.toMap(s"$nonCellStr'") == yCell)

  }

}
