package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.{NameEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.formulas.{Sort, StandardSorts}
import at.forsyte.apalache.tla.lir.values.{TlaRealSet, TlaStrSet}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.UninterpretedSort

@RunWith(classOf[JUnitRunner])
class TestJudgement extends FunSuite {

  def CustomSort(id: Int): UninterpretedSort = UninterpretedSort(s"S$id")

  val constantMap: ConstSetMapT = Map(
      "x" -> CustomSort(1),
      "y" -> CustomSort(2),
      "z" -> UninterpretedSort("ZSORT"),
  )

  val allowed: Seq[TlaEx] = (Seq(
      tla.intSet(),
      tla.natSet(),
      tla.booleanSet(),
  ) map { _.untyped() }) ++ (constantMap.keys.toSeq.map { tla.name(_).untyped() })

  val disallowed: Seq[TlaEx] = Seq(
      ValEx(TlaRealSet),
      ValEx(TlaStrSet),
      tla.enumSet(tla.int(1), tla.int(2)),
      tla.dotdot(tla.int(0), tla.int(42)),
      NameEx("potato"),
  )

  val judgement = new RestrictedSetJudgement(constantMap)

  test("Restricted set recognition") {
    allowed.foreach { ex =>
      assert(judgement.isRestrictedSet(ex))
    }

    disallowed.foreach { ex =>
      assert(!judgement.isRestrictedSet(ex))
    }

  }

  test("Restricted set Sort recognition") {
    val expected: Map[TlaEx, Sort] = Map(
        tla.intSet().untyped() -> StandardSorts.IntSort(),
        tla.natSet().untyped() -> StandardSorts.IntSort(),
        tla.booleanSet().untyped() -> StandardSorts.BoolSort(),
    ) ++ (constantMap map { case (k, v) => tla.name(k).untyped() -> v })

    allowed.foreach { ex =>
      assert(judgement.getSort(ex) == expected(ex))
    }

    disallowed.foreach { ex =>
      assertThrows[RewriterException] {
        judgement.getSort(ex)
      }
    }
  }
}
