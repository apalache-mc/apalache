package at.forsyte.apalache.tla.passes.pp

import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, LanguageWatchdog}
import at.forsyte.apalache.tla.lir.TlaModule
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

class WatchdogPassImpl @Inject() (val pred: LanguagePred) extends WatchdogPass with LazyLogging {

  override def name: String = "WatchdogPass"

  override def execute(module: TlaModule): PassResult = {
    // Only call the watchdog, then return true, don't change the module in any way
    LanguageWatchdog(pred).check(module)

    Right(module)
  }

  override def dependencies = Set()

  override def transformations = Set()
}
