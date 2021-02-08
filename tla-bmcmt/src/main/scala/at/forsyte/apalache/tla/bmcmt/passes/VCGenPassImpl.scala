package at.forsyte.apalache.tla.bmcmt.passes

import java.io.File
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.bmcmt.{CheckerException, VCGenerator}
import at.forsyte.apalache.tla.lir.NullEx
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * The pass that generates verification conditions.
 *
 * @author Igor Konnov
 */
class VCGenPassImpl @Inject() (options: PassOptions, tracker: TransformationTracker,
    @Named("AfterVCGen") nextPass: Pass with TlaModuleMixin)
    extends VCGenPass with LazyLogging {

  /**
   * The pass name.
   *
   * @return the name associated with the pass
   */
  override def name: String = "VCGen"

  /**
   * Run the pass.
   *
   * @return true, if the pass was successful
   */
  override def execute(): Boolean = {
    if (tlaModule.isEmpty) {
      throw new CheckerException(s"The input of $name pass is not initialized", NullEx)
    }

    val newModule =
      options.get[List[String]]("checker", "inv") match {
        case Some(invariants) =>
          invariants.foldLeft(tlaModule.get) { (mod, invName) =>
            logger.info(s"  > Producing verification conditions from the invariant $invName")
            new VCGenerator(tracker).gen(mod, invName)
          }
        case None =>
          logger.info("  > No invariant given. Only deadlocks will be checked")
          tlaModule.get
      }

    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    PrettyWriter.write(newModule, new File(outdir.toFile, "out-vcgen.tla"))

    nextPass.setModule(newModule)
    true
  }

  /**
   * Get the next pass in the chain. What is the next pass is up
   * to the module configuration and the pass outcome.
   *
   * @return the next pass, if exists, or None otherwise
   */
  override def next(): Option[Pass] = {
    Some(nextPass)
  }
}
