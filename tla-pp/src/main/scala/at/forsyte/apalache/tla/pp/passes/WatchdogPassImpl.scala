package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, LanguageWatchdog}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

class WatchdogPassImpl @Inject() (val options: PassOptions, val pred: LanguagePred,
    @Named("AfterWatchdog") nextPass: Pass with TlaModuleMixin)
    extends WatchdogPass with LazyLogging {

  /**
   * The pass name.
   *
   * @return the name associated with the pass
   */
  override def name: String = "WatchdogPass"

  /**
   * Run the pass.
   *
   * @return true, if the pass was successful
   */
  override def execute(): Boolean = {
    val module = tlaModule.get

    // Only call the watchdog, then return true, don't change the module in any way
    LanguageWatchdog(pred).check(module)

    true
  }

  /**
   * Get the next pass in the chain. What is the next pass is up
   * to the module configuration and the pass outcome.
   *
   * @return the next pass, if exists, or None otherwise
   */
  override def next(): Option[Pass] = {
    tlaModule map { m =>
      nextPass.setModule(m)
      nextPass
    }
  }
}
