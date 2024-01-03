package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist.opt

class SimulateCmd extends CheckCmd(name = "simulate", "Symbolically simulate a TLA+ specification") {
  var maxRun: Int =
    opt[Int](name = "max-run",
        description =
          "do not stop after a first simulation run, but produce up to a given number of runs (unless reached --max-error), default: 100",
        default = 100)

  override def toConfig() = {
    val newTuningOptions = Map(
        "search.simulation" -> "true",
        "search.simulation.maxRun" -> maxRun.toString,
    )
    for {
      cfg <- super.toConfig()
      tuning = cfg.checker.tuning.map(m => m ++ newTuningOptions)
    } yield cfg.copy(checker = cfg.checker.copy(tuning = tuning))
  }
}
