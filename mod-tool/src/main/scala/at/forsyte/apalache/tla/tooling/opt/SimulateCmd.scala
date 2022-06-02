package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist.opt

class SimulateCmd extends CheckCmd(name = "simulate", "Symbolically simulate a TLA+ specification") {
  var maxRun: Int =
    opt[Int](name = "max-run",
        description =
          "do not stop after a first simulation run, but produce up to a given number of runs (unless reached --max-error), default: 100",
        default = 100)

  var saveRuns: Boolean =
    opt[Boolean](name = "save-runs", description = "save an example trace for each simulated run, default: false",
        default = false)

}
