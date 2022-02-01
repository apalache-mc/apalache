package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.NullEx
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, LanguageWatchdog}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * The reTLA to VMT transpilation pass
 *
 * @author Jure Kukovec
 */
class ReTLAToVMTTranspilePassImpl @Inject() (val options: PassOptions, pred: LanguagePred,
    @Named("AfterConstraintGen") val nextPass: Pass with TlaModuleMixin)
    extends TranspilePass with LazyLogging {

  override def name: String = "Transpiler"

  // TODO
  override def execute(): Boolean = {
    if (tlaModule.isEmpty) {
      throw new CheckerException(s"The input of $name pass is not initialized", NullEx)
    }
    val module = tlaModule.get

    // Check if still ok fragment (sanity check, see postTypeChecker)
    LanguageWatchdog(pred).check(module)
    nextPass.updateModule(this, tlaModule, module)

    true
  }

  override def dependencies = Set()
  override def transformations = Set()
}
