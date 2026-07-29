package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.io.config.Constants.{MAX_ERROR, MAX_RUN, SIMULATE}
import at.forsyte.apalache.io.config.{ApalacheConfig, CheckerPatch, ConfigParseResult}
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams
import org.backuity.clist.opt

class SimulateCmd extends CheckCmd(name = SIMULATE, "Symbolically simulate a TLA+ specification") {
  var maxRun: Option[Int] =
    opt[Option[Int]](name = MAX_RUN,
        description = descriptionWithDefault(
            s"do not stop after a first simulation run, but produce up to a given number of runs " +
              s"(unless reached --$MAX_ERROR)",
            ModelCheckerParams.defaultSimulationRuns,
        ), default = None)

  override def toConfig: ConfigParseResult[ApalacheConfig] = {
    val simulationOptions = maxRun match {
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
        ApalacheConfig(checker = CheckerPatch(tuning = Some(simulationOptions))),
    )
  }
}
