package at.forsyte.apalache.tla.bmcmt.stratifiedRules

import at.forsyte.apalache.tla.bmcmt.{ArenaCell, Binding, PureArena}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.RewriterScope
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class FunRewriterTest extends AnyFunSuite with BeforeAndAfterEach {

  var rewriter: TestingRewriter = TestingRewriter(Map.empty)

  override def beforeEach(): Unit = {
    rewriter = TestingRewriter(Map.empty)
  }

  test("FunCtor") {

    // Deferred until <<p,p>> rewriting is complete, as function rewriting creates a set of pairs

//    // Load up the arena with 2 var cells
//    val (Seq(xCell, yCell), arena) = Seq(IntT1, IntT1).foldLeft((Seq.empty[ArenaCell], PureArena.initial)) {
//      case ((seq, partialArena), cellT) =>
//        val (newArena, newCell) = addCell(partialArena, cellT)
//        (seq :+ newCell, newArena)
//    }
//
//    val set = tla.enumSet(tla.name("x", IntT1), tla.name("y", IntT1))
//    val ex = tla.funDef(tla.name("p", IntT1), tla.name("p", IntT1) -> set)
//
//    val startScope = RewriterScope(arena, Binding(Map("x" -> xCell, "y" -> yCell)))
//
//    val (endScope, cell) = rewriter.rewrite(ex)(startScope)
//s
  }

}
