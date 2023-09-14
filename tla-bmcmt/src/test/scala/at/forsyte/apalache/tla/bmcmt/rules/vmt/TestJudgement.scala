package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.lir.values.{TlaRealSet, TlaStrSet}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestJudgement extends AnyFunSuite {

  def CustomSort(id: Int): UninterpretedSort = UninterpretedSort(s"S$id")

  val constantMap: ConstSetMapT = Map(
      "x" -> CustomSort(1),
      "y" -> CustomSort(2),
      "z" -> UninterpretedSort("ZSORT"),
  )

  val constantMapKeyExs: Seq[TlaEx] = constantMap.keys.toSeq.map { tla.name(_, ConstT1("X")) }.map { _.build }

  val allowed: Seq[TlaEx] = Seq(
      tla.intSet(),
      tla.natSet(),
      tla.booleanSet(),
  ).map { _.build } ++ constantMapKeyExs

  val disallowed: Seq[TlaEx] = Seq(
      ValEx(TlaRealSet)(Typed(SetT1(RealT1))),
      ValEx(TlaStrSet)(Typed(SetT1(StrT1))),
      tla.enumSet(tla.int(1), tla.int(2)),
      tla.dotdot(tla.int(0), tla.int(42)),
      tla.name("potato", SetT1(IntT1)),
  )

  val judgement: RestrictedSetJudgement = new RestrictedSetJudgement(constantMap)

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
        tla.intSet().build -> IntSort,
        tla.natSet().build -> IntSort,
        tla.booleanSet().build -> BoolSort,
    ) ++ (constantMap.map { case (k, v) => tla.name(k, ConstT1("X")).build -> v })

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
