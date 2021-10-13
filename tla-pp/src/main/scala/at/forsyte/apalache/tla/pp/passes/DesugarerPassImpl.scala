package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.TlaModule
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
    @Named("AfterDesugarer") nextPass: Pass with TlaModuleMixin
) extends DesugarerPass with LazyLogging {

  private var outputTlaModule: Option[TlaModule] = None

  /**
   * The pass name.
   *
   * @return the name associated with the pass
   */
  override def name: String = "DesugarerPass"

  /**
   * Run the pass.
   *
   * @return true, if the pass was successful
   */
  override def execute(): Boolean = {
    logger.info("  > Desugaring...")
    val input = tlaModule.get
    val afterDesug = ModuleByExTransformer(Desugarer(gen, tracker))(input)
    val output = ModuleByExTransformer(SelectSeqAsFold(gen, tracker))(afterDesug)

    // dump the result of preprocessing
    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    writerFactory.writeModuleAllFormats(output.copy(name = "03_OutDesugarer"), TlaWriter.STANDARD_MODULES,
        outdir.toFile)
    outputTlaModule = Some(output)

    true
  }

  /**
   * Get the next pass in the chain. What is the next pass is up
   * to the module configuration and the pass outcome.
   *
   * @return the next pass, if exists, or None otherwise
   */
  override def next(): Option[Pass] = {
    outputTlaModule map { m =>
      nextPass.setModule(m)
      nextPass
    }
  }
}
