package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
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
    @Named("AfterConstraintGen") nextPass: Pass)
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

    true
  }

  /**
   * Get the next pass in the chain. What is the next pass is up
   * to the module configuration and the pass outcome.
   *
   * @return the next pass, if exists, or None otherwise
   */
  override def next(): Option[Pass] =
    tlaModule map { _ => nextPass }
}
