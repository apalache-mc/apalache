package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.{NameEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.formulas.{Sort, StandardSorts}
import at.forsyte.apalache.tla.lir.values.{TlaBoolSet, TlaIntSet, TlaNatSet, TlaRealSet, TlaStrSet}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla

@RunWith(classOf[JUnitRunner])
class TestJudgement extends FunSuite {

  sealed case class CustomSort(id: Int) extends Sort("")

  test("Restricted set recognition") {
    val constantMap = Map(
        "x" -> StandardSorts.BoolSort(),
        "y" -> StandardSorts.IntSort(),
        "z" -> CustomSort(1),
    )
    val judgement = new RestrictedSetJudgement(constantMap)

    val allowed: Seq[TlaEx] = (Seq(
        TlaIntSet,
        TlaNatSet,
        TlaBoolSet,
    ) map { ValEx(_) }) ++ constantMap.keys.toSeq.map { NameEx(_) }

    val disallowed: Seq[TlaEx] = Seq(
        ValEx(TlaRealSet),
        ValEx(TlaStrSet),
        tla.enumSet(tla.int(1), tla.int(2)),
        tla.dotdot(tla.int(0), tla.int(42)),
        NameEx("potato"),
    )

    allowed.foreach { ex =>
      assert(judgement.isRestrictedSet(ex))
    }

    disallowed.foreach { ex =>
      assert(!judgement.isRestrictedSet(ex))
    }

  }
}
