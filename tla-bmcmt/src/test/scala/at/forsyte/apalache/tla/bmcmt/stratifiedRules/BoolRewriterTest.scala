package at.forsyte.apalache.tla.bmcmt.stratifiedRules

import at.forsyte.apalache.tla.bmcmt.{ArenaCell, Binding, PureArena}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.{tlaU => tla}
import at.forsyte.apalache.tla.typecomp._
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class BoolRewriterTest extends AnyFunSuite with BeforeAndAfterEach {

  var rewriter: TestingRewriter = TestingRewriter(Map.empty)

  override def beforeEach(): Unit = {
    rewriter = TestingRewriter(Map.empty)
  }

  test("Boolean constant rewriting rule: FALSE ~~> $C$0 / TRUE ~~> $C$1") {
    val falseEx = tla.bool(false)
    val trueEx = tla.bool(true)

    val falseCell = rewriter.rewrite(falseEx)(RewriterScope.initial())._2
    assert(falseCell.toNameEx.eqTyped(NameEx("$C$0")(Typed(BoolT1))))

    val trueCell = rewriter.rewrite(trueEx)(RewriterScope.initial())._2
    assert(trueCell.toNameEx.eqTyped(NameEx("$C$1")(Typed(BoolT1))))
  }

  test("Boolean set rewriting rule: BOOLEAN ~~> $C$2") {
    val boolSetEx = tla.booleanSet()

    val cell = rewriter.rewrite(boolSetEx)(RewriterScope.initial())._2
    assert(cell.toNameEx.eqTyped(NameEx("$C$2")(Typed(SetT1(BoolT1)))))
  }

  test("Boolean operator rewriting rule: c_x /\\ c_y") {
    // Load up the arena with 2 var cells
    val (Seq(xCell, yCell), arena) = Seq(BoolT1, BoolT1).foldLeft((Seq.empty[ArenaCell], PureArena.initial)) {
      case ((seq, partialArena), cellT) =>
        val (newArena, newCell) = addCell(partialArena, cellT)
        (seq :+ newCell, newArena)
    }

    val x = tla.name("x", BoolT1)
    val y = tla.name("y", BoolT1)
    val expr = tla.and(x, y)

    val binding = Binding(Map("x" -> xCell, "y" -> yCell))

    val startScope = RewriterScope(arena, binding)

    // Rewrite normal 'and'
    val (_, endCell) = rewriter.rewrite(expr)(startScope)

    assert(rewriter.assertSeq ==
      Seq(
          tla.eql(endCell.toBuilder, tla.and(xCell.toBuilder, yCell.toBuilder)).build
      ))

    rewriter.assertSeq = Seq.empty

    // Check that adding spurious TRUEs doesn't affect the rewriting
    val exprWithTrues = tla.and(tla.bool(true), x, tla.bool(true), y, tla.bool(true))
    val (_, endCell2) = rewriter.rewrite(exprWithTrues)(startScope)

    assert(rewriter.assertSeq ==
      Seq(
          tla.eql(endCell2.toBuilder, tla.and(xCell.toBuilder, yCell.toBuilder)).build
      ))

    rewriter.assertSeq = Seq.empty

    // Check that adding one FALSE makes the whole thing false
    val exprWithFalse = tla.and(tla.bool(true), x, tla.bool(false), y, tla.bool(true))
    val (_, endCell3) = rewriter.rewrite(exprWithFalse)(startScope)

    assert(rewriter.assertSeq.isEmpty)
    assert(endCell3 == PureArena.cellFalse(arena))

  }

  test("Boolean operator rewriting rule: c_x \\/ c_y") {
    // Load up the arena with 2 var cells
    val (Seq(xCell, yCell), arena) = Seq(BoolT1, BoolT1).foldLeft((Seq.empty[ArenaCell], PureArena.initial)) {
      case ((seq, partialArena), cellT) =>
        val (newArena, newCell) = addCell(partialArena, cellT)
        (seq :+ newCell, newArena)
    }

    val x = tla.name("x", BoolT1)
    val y = tla.name("y", BoolT1)
    val expr = tla.or(x, y)

    val binding = Binding(Map("x" -> xCell, "y" -> yCell))

    val startScope = RewriterScope(arena, binding)

    // Rewrite normal 'or'
    val (_, endCell) = rewriter.rewrite(expr)(startScope)

    assert(rewriter.assertSeq ==
      Seq(
          tla.eql(endCell.toBuilder, tla.or(xCell.toBuilder, yCell.toBuilder)).build
      ))

    rewriter.assertSeq = Seq.empty

    // Check that adding spurious FALSEs doesn't affect the rewriting
    val exprWithFalses = tla.or(tla.bool(false), x, tla.bool(false), y, tla.bool(false))
    val (_, endCell2) = rewriter.rewrite(exprWithFalses)(startScope)

    assert(rewriter.assertSeq ==
      Seq(
          tla.eql(endCell2.toBuilder, tla.or(xCell.toBuilder, yCell.toBuilder)).build
      ))

    rewriter.assertSeq = Seq.empty

    // Check that adding one TRUE makes the whole thing true
    val exprWithTrue = tla.or(tla.bool(false), x, tla.bool(true), y, tla.bool(false))
    val (_, endCell3) = rewriter.rewrite(exprWithTrue)(startScope)

    assert(rewriter.assertSeq.isEmpty)
    assert(endCell3 == PureArena.cellTrue(arena))

  }

}
