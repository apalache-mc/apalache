package at.forsyte.apalache.tla.passes.pp

import at.forsyte.apalache.infra.ExitCodes
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{TlaDecl, TlaModule, TlaOperDecl, UID}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.{
  LanguagePred, PredResultFail, PredResultOk, TlaModuleTransformation, TransformationTracker,
}
import at.forsyte.apalache.tla.lir.transformations.standard.{
  IncrementalRenaming, ModuleByExTransformer, PrimePropagation,
}
import at.forsyte.apalache.infra.passes.DerivedPredicates
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.options.OptionGroup

abstract class PreproPassPartial(
    val options: OptionGroup.HasChecker,
    derivedPreds: DerivedPredicates,
    renaming: IncrementalRenaming,
    tracker: TransformationTracker,
    sourceStore: SourceStore,
    changeListener: ChangeListener,
    writerFactory: TlaWriterFactory)
    extends PreproPass with LazyLogging {
  override def name: String = "PreprocessingPass"

  protected def writeAndReturn(module: TlaModule): TlaModule = {
    writeOut(writerFactory, module)
    module
  }

  protected def applyTx(
      input: TlaModule,
      transformationSequence: List[(String, TlaModuleTransformation)],
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

  protected def checkLocations(module: TlaModule): Unit = {
    // when --debug is enabled, check that all identifiers are assigned a location
    if (options.common.debug) {
      val sourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)
      module.operDeclarations.foreach(sourceLocator.checkConsistency)
    }
  }

  protected def postLanguageCheck(tlaModule: TlaModule, lPred: LanguagePred): PassResult =
    // check, whether all expressions fit in the language
    lPred.isModuleOk(tlaModule) match {
      case PredResultOk() =>
        Right(tlaModule)

      case PredResultFail(failedIds) =>
        for ((id, errorMessage) <- failedIds) {
          val message = "%s: unsupported expression: %s".format(findLoc(id), errorMessage)
          logger.error(message)
        }
        val errData = failedIds.map { case (uid, s) => (uid.toString(), s) }
        passFailure(errData, ExitCodes.FAILURE_SPEC_EVAL)
    }

  protected def executeWithParams(
      tlaModule: TlaModule,
      transformationSequence: List[(String, TlaModuleTransformation)],
      postRename: Boolean,
      lPred: LanguagePred): PassResult = {
    val afterModule = applyTx(tlaModule, transformationSequence, postRename)

    checkLocations(tlaModule)

    postLanguageCheck(afterModule, lPred)
  }

  protected def createModuleTransformerForPrimePropagation(varSet: Set[String]): ModuleByExTransformer = {
    val cinitName = derivedPreds.cinit.getOrElse("CInit") + "Primed" // TODO Why does this default?
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
