package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.ModuleByExTransformer
import at.forsyte.apalache.tla.pp.Desugarer
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

class PreproPassImpl @Inject()(val options: PassOptions,
                               tracker: TransformationTracker,
                               @Named("AfterPrepro") nextPass: Pass with TlaModuleMixin)
    extends PreproPass with LazyLogging {

  override var tlaModule: Option[TlaModule] = None
  private var outputTlaModule: Option[TlaModule] = None

  /**
    * The pass name.
    *
    * @return the name associated with the pass
    */
  override def name: String = "PreprocessingPass"

  /**
    * Run the pass.
    *
    * @return true, if the pass was successful
    */
  override def execute(): Boolean = {
    logger.info("de-sugaring the spec")
    val afterDesugarer = ModuleByExTransformer(Desugarer(tracker)) (tlaModule.get)
    outputTlaModule = Some(afterDesugarer)
    true
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    if (outputTlaModule.isDefined) {
      nextPass.tlaModule = outputTlaModule
      Some(nextPass)
    } else {
      None
    }
  }

}
