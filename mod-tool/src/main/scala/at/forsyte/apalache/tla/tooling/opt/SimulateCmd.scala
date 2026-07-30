package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.io.config.{ApalacheConfig, CheckerPatch, ConfigParseResult}
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams
import org.backuity.clist.opt

class SimulateCmd extends CheckCmd(name = "simulate", "Symbolically simulate a TLA+ specification") {
  var maxRun: Option[Int] =
    opt[Option[Int]](name = "max-run",
        description = descriptionWithDefault(
            "do not stop after a first simulation run, but produce up to a given number of runs (unless reached --max-error)",
            ModelCheckerParams.defaultSimulationRuns,
        ), default = None)

  override def toConfig: ConfigParseResult[ApalacheConfig] = {
    val tuning = maxRun match {
      case Some(value) =>
        Map(
            "search.simulation" -> "true",
            "search.simulation.maxRun" -> value.toString,
        )
      case None =>
        Map("search.simulation" -> "true")
    }
    mergeConfig(
        super.toConfig,
        ApalacheConfig(checker = CheckerPatch(tuning = Some(tuning))),
    )
  }
}
