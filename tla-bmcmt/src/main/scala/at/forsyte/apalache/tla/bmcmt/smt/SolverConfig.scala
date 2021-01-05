package at.forsyte.apalache.tla.bmcmt.smt

/**
  * Configuration option to be passed to SolverContext. This class is declared as a case class
  * to enable the concise copy syntax of Scala.
  *
  * @param debug Enable the debug mode (activated with --debug). Write the log file to log%d.smt.
  * @param profile Enable the profile mode (activated with --profile). Report the metrics.
  * @param randomSeed The random seed to be passed to z3 as :random-seed.
  *
  * @author Igor Konnov
  */
sealed case class SolverConfig(debug: Boolean,
                               profile: Boolean,
                               randomSeed: Int) {
}

object SolverConfig {
  /**
    * Get the default configuration.
    */
  val default: SolverConfig = new SolverConfig(debug = false, profile = false, randomSeed = 0)
}