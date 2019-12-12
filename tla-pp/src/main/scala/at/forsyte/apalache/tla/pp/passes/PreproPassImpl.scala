package at.forsyte.apalache.tla.pp.passes

import java.io.File
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.transformations.{TlaModuleTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.pp.{Desugarer, Keramelizer, Normalizer, UniqueNameGenerator}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * A preprocessing pass that simplifies TLA+ expression by running multiple transformation.
  * @param options pass options
  * @param gen name generator
  * @param tracker transformation tracker
  * @param nextPass next pass to call
  */
class PreproPassImpl @Inject()( val options: PassOptions,
                                gen: UniqueNameGenerator,
                                renaming: IncrementalRenaming,
                                tracker: TransformationTracker,
                                @Named("AfterPrepro") nextPass: Pass with TlaModuleMixin)
    extends PreproPass with LazyLogging {

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
    logger.info("  > Before preprocessing: unique renaming")
    val input = tlaModule.get

    val transformationSequence: List[(String, TlaModuleTransformation)] =
      List(
        ("Desugarer", ModuleByExTransformer(Desugarer(tracker))),
        ("UniqueRenamer", renaming.renameInModule),
        ("Normalizer", ModuleByExTransformer(Normalizer(tracker))),
        ("Keramelizer", ModuleByExTransformer(Keramelizer(gen, tracker)))
      )

    logger.info(" > Applying standard transformations:")
    val preprocessed = transformationSequence.foldLeft(input) {
      case (m, (name, xformer)) =>
        logger.info(s"  > $name")
        xformer(m)
    }

    // unique renaming after all transformations
    logger.info("  > After preprocessing: UniqueRenamer")
    val afterModule = renaming.renameInModule(preprocessed)

    // dump the result of preprocessing
    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    PrettyWriter.write(afterModule, new File(outdir.toFile, "out-prepro.tla"))

    outputTlaModule = Some(afterModule)
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
      nextPass.setModule( m )
      nextPass
    }
  }
}
