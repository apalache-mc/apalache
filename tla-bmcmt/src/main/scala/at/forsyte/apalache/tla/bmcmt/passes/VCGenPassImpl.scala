package at.forsyte.apalache.tla.bmcmt.passes

import java.io.File
import java.nio.file.Path
import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.bmcmt.{CheckerException, VCGenerator}
import at.forsyte.apalache.tla.lir.NullEx
import at.forsyte.apalache.tla.lir.{TlaModule, ModuleProperty}
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * The pass that generates verification conditions.
 *
 * @author Igor Konnov
 */
class VCGenPassImpl @Inject() (options: PassOptions, tracker: TransformationTracker, writerFactory: TlaWriterFactory,
    @Named("AfterVCGen") val nextPass: Pass with TlaModuleMixin)
    extends VCGenPass with LazyLogging {

  override def name: String = "VCGen"

  override def execute(): Boolean = {
    if (tlaModule.isEmpty) {
      throw new CheckerException(s"The input of $name pass is not initialized", NullEx)
    }

    val newModule =
      options.get[List[String]]("checker", "inv") match {
        case Some(invariants) =>
          invariants.foldLeft(rawModule.get) { (mod, invName) =>
            logger.info(s"  > Producing verification conditions from the invariant $invName")
            val optViewName = options.get[String]("checker", "view")
            if (optViewName.isDefined) {
              logger.info(s"  > Using state view ${optViewName.get}")
            }
            new VCGenerator(tracker).gen(mod, invName, optViewName)
          }
        case None =>
          logger.info("  > No invariant given. Only deadlocks will be checked")
          tlaModule.get
      }

    writerFactory.writeModuleAllFormats(newModule.copy(name = "07_OutVCGen"), TlaWriter.STANDARD_MODULES)

    nextPass.updateModule(this, newModule)
    true
  }

  override def dependencies = Set(ModuleProperty.Inlined)

  override def transformations = Set(ModuleProperty.VCGenerated)
}
