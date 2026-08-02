package at.forsyte.apalache.tla.bmcmt.search

import at.forsyte.apalache.io.config.SearchKind
import at.forsyte.apalache.tla.bmcmt.{CheckerInput, CheckerInputVC}
import at.forsyte.apalache.tla.lir.TlaModule
import org.scalatest.funsuite.AnyFunSuite

class TestSearchState extends AnyFunSuite {
  private val checkerInput = new CheckerInput(
      TlaModule("root", List()),
      initTransitions = List(),
      nextTransitions = List(),
      constInitPrimed = None,
      verificationConditions = CheckerInputVC(List()),
  )

  test("uses the resolved run count") {
    val check = new SearchState(params(SearchKind.Check, maxRun = 1))
    val simulate = new SearchState(params(SearchKind.Simulate, maxRun = 7))

    assert(check.nRunsLeft == 1)
    assert(simulate.nRunsLeft == 7)

    simulate.onRunDone()
    assert(simulate.nRunsLeft == 6)
  }

  private def params(searchKind: SearchKind, maxRun: Int): ModelCheckerParams =
    new ModelCheckerParams(checkerInput, 0, Map(), searchKind, seed = 0, maxRun = maxRun, outputTraces = false)
}
