package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{TlaDecl, TlaModule, TlaOperDecl, UID}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.{
  LanguagePred, PredResultFail, PredResultOk, TlaModuleTransformation, TransformationTracker,
}
import at.forsyte.apalache.tla.lir.transformations.standard.{
  IncrementalRenaming, ModuleByExTransformer, PrimePropagation,
}
import com.typesafe.scalalogging.LazyLogging

abstract class PreproPassPartial(
    val options: PassOptions, renaming: IncrementalRenaming, tracker: TransformationTracker, sourceStore: SourceStore,
    changeListener: ChangeListener, writerFactory: TlaWriterFactory, nextPass: Pass with TlaModuleMixin,
) extends PreproPass with LazyLogging {
  private var outputTlaModule: Option[TlaModule] = None

  override def name: String = "PreprocessingPass"

  protected def writeAndReturn(module: TlaModule): TlaModule = {
    writerFactory.writeModuleAllFormats(module.copy(name = "08_OutPrepro"), TlaWriter.STANDARD_MODULES)
    module
  }

  protected def applyTx(input: TlaModule, transformationSequence: List[(String, TlaModuleTransformation)],
      postRename: Boolean = false): TlaModule = {
    logger.info(" > Applying standard transformations:")
    val preprocessed = transformationSequence.foldLeft(input) { case (m, (name, xformer)) =>
      logger.info(s"  > $name")
      val transfomed = xformer(m)
      // dump the result of preprocessing after every transformation, in case the next one fails
      writeAndReturn(transfomed)
    }
    if (postRename) {
      // unique renaming after all transformations
      logger.info("  > After preprocessing: UniqueRenamer")
      // dump the result of preprocessing
      val ret = renaming.renameInModule(preprocessed)
      writeAndReturn(ret)
    } else preprocessed
  }

  protected def checkLocations(): Unit = {
    // when --debug is enabled, check that all identifiers are assigned a location
    if (options.getOrElse[Boolean]("general", "debug", false)) {
      val sourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)
      outputTlaModule.get.operDeclarations foreach sourceLocator.checkConsistency
    }
  }

  protected def postLanguageCheck(lPred: LanguagePred): Boolean =
    // check, whether all expressions fit in the language
    lPred.isModuleOk(outputTlaModule.get) match {
      case PredResultOk() =>
        true

      case PredResultFail(failedIds) =>
        for ((id, errorMessage) <- failedIds) {
          val message = "%s: unsupported expression: %s".format(findLoc(id), errorMessage)
          logger.error(message)
        }
        false
    }

  protected def executeWithParams(transformationSequence: List[(String, TlaModuleTransformation)], postRename: Boolean,
      lPred: LanguagePred): Boolean = {
    val input = tlaModule.get

    val afterModule = applyTx(input, transformationSequence, postRename)

    outputTlaModule = Some(afterModule)
    nextPass.updateModule(this, afterModule)

    checkLocations()

    postLanguageCheck(lPred)
  }

  protected def createModuleTransformerForPrimePropagation(varSet: Set[String]): ModuleByExTransformer = {
    val cinitName = options.getOrElse[String]("checker", "cinit", "CInit") + "Primed"
    val includeAllButConstInit: TlaDecl => Boolean = {
      case TlaOperDecl(name, _, _) => cinitName != name
      case _                       => true
    }
    ModuleByExTransformer(new PrimePropagation(tracker, varSet), includeAllButConstInit)
  }

  private def findLoc(id: UID): String = {
    val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

    sourceLocator.sourceOf(id) match {
      case Some(loc) => loc.toString
      case None      => "<unknown>"
    }
  }

}
