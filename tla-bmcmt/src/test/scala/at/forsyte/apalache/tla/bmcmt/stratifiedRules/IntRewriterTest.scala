package at.forsyte.apalache.tla.bmcmt.stratifiedRules

import at.forsyte.apalache.tla.lir.{IntT1, NameEx, SetT1, Typed}
import at.forsyte.apalache.tla.types.{tlaU => tla}
import at.forsyte.apalache.tla.typecomp._
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class IntRewriterTest extends AnyFunSuite with BeforeAndAfterEach {

  var rewriter: TestingRewriter = TestingRewriter(Map.empty)

  override def beforeEach(): Unit = {
    rewriter = TestingRewriter(Map.empty)
  }

  test("Integer set rewriting rule: Nat ~~> $C$3 / Int ~~> $C$4") {
    val natSetEx = tla.natSet()
    val intSetEx = tla.intSet()

    val cellNat = rewriter.rewrite(natSetEx)(RewriterScope.initial())._2
    assert(cellNat.toNameEx.eqTyped(NameEx("$C$3")(Typed(SetT1(IntT1)))))

    val cellInt = rewriter.rewrite(intSetEx)(RewriterScope.initial())._2
    assert(cellInt.toNameEx.eqTyped(NameEx("$C$4")(Typed(SetT1(IntT1)))))
  }

  test("Integer constant rewriting rule.") {
    val i1 = tla.int(0)
    val i2 = tla.int(42)

    val initScope = RewriterScope.initial()

    val (scope1, cell1) = rewriter.rewrite(i1)(initScope)

    assert(
        rewriter.assertSeq == Seq(tla.eql(cell1.toBuilder, i1).build)
    )

    val (_, cell2) = rewriter.rewrite(i2)(scope1)

    assert(
        rewriter.assertSeq == Seq(
            tla.eql(cell1.toBuilder, i1),
            tla.eql(cell2.toBuilder, i2),
        ).map(_.build)
    )

  }

}
