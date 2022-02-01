package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, LanguageWatchdog}
import at.forsyte.apalache.tla.lir.ModuleProperty
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

class WatchdogPassImpl @Inject() (val options: PassOptions, val pred: LanguagePred,
    @Named("AfterWatchdog") val nextPass: Pass with TlaModuleMixin)
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

    // Copy the module to next pass
    nextPass.updateModule(this, tlaModule, module)

    true
  }

  override def dependencies = Set()

  override def transformations = Set()
}
