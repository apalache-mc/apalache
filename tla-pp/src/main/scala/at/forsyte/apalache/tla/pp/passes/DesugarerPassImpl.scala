package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.{TlaModule, ModuleProperty}
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.pp.{Desugarer, SelectSeqAsFold, UniqueNameGenerator}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

import java.io.File
import java.nio.file.Path

/**
 * Desugarer pass.
 *
 * @param options  pass options
 * @param tracker  transformation tracker
 * @param nextPass next pass to call
 */
class DesugarerPassImpl @Inject() (
    val options: PassOptions, tracker: TransformationTracker, gen: UniqueNameGenerator, writerFactory: TlaWriterFactory,
    @Named("AfterDesugarer") val nextPass: Pass with TlaModuleMixin,
) extends DesugarerPass with LazyLogging {

  override def name: String = "DesugarerPass"

  override def execute(): Boolean = {
    logger.info("  > Desugaring...")
    val input = tlaModule.get
    val afterDesug = ModuleByExTransformer(Desugarer(gen, tracker))(input)
    val output = ModuleByExTransformer(SelectSeqAsFold(gen, tracker))(afterDesug)

    // dump the result of preprocessing
    writerFactory.writeModuleAllFormats(output.copy(name = "03_OutDesugarer"), TlaWriter.STANDARD_MODULES)
    nextPass.updateModule(this, output)

    true
  }

  override def dependencies = Set(ModuleProperty.TypeChecked)

  override def transformations = Set(ModuleProperty.Desugared)
}
