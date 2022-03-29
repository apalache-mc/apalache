package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, LanguageWatchdog}
import at.forsyte.apalache.tla.lir.TlaModule
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

class WatchdogPassImpl @Inject() (val options: PassOptions, val pred: LanguagePred)
    extends WatchdogPass with LazyLogging {

  override def name: String = "WatchdogPass"

  override def execute(module: TlaModule): Option[TlaModule] = {
    // Only call the watchdog, then return true, don't change the module in any way
    LanguageWatchdog(pred).check(module)

    Some(module)
  }

  override def dependencies = Set()

  override def transformations = Set()
}
