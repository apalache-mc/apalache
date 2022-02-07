package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, LanguageWatchdog}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * The reTLA to VMT transpilation pass
 *
 * @author Jure Kukovec
 */
class ReTLAToVMTTranspilePassImpl @Inject() (val options: PassOptions, pred: LanguagePred)
    extends TranspilePass with LazyLogging {

  override def name: String = "Transpiler"

  // TODO
  override def execute(module: TlaModule): Option[TlaModule] = {
    // Check if still ok fragment (sanity check, see postTypeChecker)
    LanguageWatchdog(pred).check(module)

    Some(module)
  }

  override def dependencies = Set()
  override def transformations = Set()
}
