package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.transformations.{
  PredResultFail, PredResultOk, TlaModuleTransformation, TransformationTracker
}
import at.forsyte.apalache.tla.lir.{TlaDecl, TlaModule, TlaOperDecl, UID}
import at.forsyte.apalache.tla.pp.{Desugarer, Keramelizer, Normalizer, UniqueNameGenerator}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * A preprocessing pass that simplifies TLA+ expression by running multiple transformation.
 *
 * @param options pass options
 * @param gen     name generator
 * @param tracker  transformation tracker
 * @param nextPass next pass to call
 */
class PreproPassImpl @Inject() (
    val options: PassOptions, gen: UniqueNameGenerator, renaming: IncrementalRenaming, tracker: TransformationTracker,
    sourceStore: SourceStore, changeListener: ChangeListener, writerFactory: TlaWriterFactory,
    @Named("AfterPrepro") nextPass: Pass with TlaModuleMixin
) extends PreproPass with LazyLogging {
  val MANUAL_LINK = "https://apalache.informal.systems/docs/apalache/known-issues.html"

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
    val varSet = input.varDeclarations.map(_.name).toSet

    val transformationSequence: List[(String, TlaModuleTransformation)] =
      List(
          ("PrimePropagation", createModuleTransformerForPrimePropagation(varSet)),
          ("Desugarer", ModuleByExTransformer(Desugarer(gen, tracker))),
          ("UniqueRenamer", renaming.renameInModule),
          ("Normalizer", ModuleByExTransformer(Normalizer(tracker))),
          ("Keramelizer", ModuleByExTransformer(Keramelizer(gen, tracker)))
      )

    logger.info(" > Applying standard transformations:")
    val preprocessed = transformationSequence.foldLeft(input) { case (m, (name, xformer)) =>
      logger.info(s"  > $name")
      val transfomed = xformer(m)
      // dump the result of preprocessing after every transformation, in case the next one fails
      writerFactory.writeModuleAllFormats(transfomed.copy(name = "08_OutPrepro"), TlaWriter.STANDARD_MODULES)
      transfomed
    }

    // unique renaming after all transformations
    logger.info("  > After preprocessing: UniqueRenamer")
    val afterModule = renaming.renameInModule(preprocessed)

    // dump the result of preprocessing
    writerFactory.writeModuleAllFormats(afterModule.copy(name = "08_OutPrepro"), TlaWriter.STANDARD_MODULES)
    outputTlaModule = Some(afterModule)

    // when --debug is enabled, check that all identifiers are assigned a location
    if (options.getOrElse[Boolean]("general", "debug", false)) {
      val sourceLocator =
        SourceLocator(sourceStore.makeSourceMap, changeListener)
      outputTlaModule.get.operDeclarations foreach sourceLocator.checkConsistency
    }

    // check, whether all expressions fit in KerA+
    val shallContinue = KeraLanguagePred().isModuleOk(outputTlaModule.get) match {
      case PredResultOk() =>
        true

      case PredResultFail(failedIds) =>
        for ((id, errorMessage) <- failedIds) {
          val message = "%s: unsupported expression: %s".format(findLoc(id), errorMessage)
          logger.error(message)
        }
        false
    }

    shallContinue
  }

  private def createModuleTransformerForPrimePropagation(varSet: Set[String]): ModuleByExTransformer = {
    val cinitName = options.getOrElse[String]("checker", "cinit", "CInit") + "Primed"
    val includeAllButConstInit: TlaDecl => Boolean = {
      case TlaOperDecl(name, _, _) => cinitName != name
      case _                       => true
    }
    ModuleByExTransformer(new PrimePropagation(tracker, varSet), includeAllButConstInit)
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

  private def findLoc(id: UID): String = {
    val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

    sourceLocator.sourceOf(id) match {
      case Some(loc) => loc.toString
      case None      => "<unknown>"
    }
  }
}
