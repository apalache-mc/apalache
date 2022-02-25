package at.forsyte.apalache.tla.assignments.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.tla.assignments._
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.storage.{BodyMapFactory, ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.pp.NormalizedNames
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * This pass finds symbolic transitions in Init and Next.
 */
class TransitionPassImpl @Inject() (
    options: PassOptions,
    sourceStore: SourceStore,
    tracker: TransformationTracker,
    changeListener: ChangeListener,
    incrementalRenaming: IncrementalRenaming,
    writerFactory: TlaWriterFactory)
    extends TransitionPass with LazyLogging {

  override def name: String = "TransitionFinderPass"

  override def execute(tlaModule: TlaModule): Option[TlaModule] = {
    // extract transitions from InitPrimed
    val initOperName = options.getOrElse("checker", "init", "Init")
    val initOperNamePrimed = initOperName + "Primed"
    val initDeclarations = extractTransitions(tlaModule, initOperNamePrimed, NormalizedNames.INIT_PREFIX)
    logger.info(s"  > Found ${initDeclarations.size} initializing transitions")

    // extract transitions from Next
    val nextOperName = options.getOrElse("checker", "next", "Next")
    val nextDeclarations = extractTransitions(tlaModule, nextOperName, NormalizedNames.NEXT_PREFIX)
    logger.info(s"  > Found ${nextDeclarations.size} transitions")

    val invDeclarations: Seq[TlaDecl] = options.get[List[String]]("checker", "inv") match {
      case Some(invariants) => invariants.map { invariant => tlaModule.declarations.find(_.name == invariant).get }
      case None             => Seq()
    }

    // convert an optional CInit operator
    val cinitDeclarations =
      options.get[String]("checker", "cinit") match {
        case None =>
          logger.info(s"  > No constant initializer")
          Seq()

        case Some(cinitName) =>
          logger.info(s"  > Found constant initializer $cinitName")
          val cinitEx = findBodyOf(cinitName + "Primed", tlaModule.operDeclarations: _*)
          // We don't perform the standard assignment-search on cinit,
          // we just replace EVERY x' = e with x' <- e
          val tr = AssignmentOperatorIntroduction({ _ => true }, tracker)
          val newEx = tr(cinitEx)
          Seq(ModuleAdapter.exprToOperDef(NormalizedNames.CONST_INIT, newEx))
      }

    // Add the constants, variables, and assumptions; then add CInit, Init*, Next*; then add verification conditions.
    val vcDeclarations = tlaModule.declarations.filter(NormalizedNames.isVC)
    // In case verification conditions weren't generated yet, keep the raw invariants
    val vcDeclarationsOrInvariants = if (vcDeclarations.isEmpty) invDeclarations else vcDeclarations

    val newDecls = tlaModule.constDeclarations ++ tlaModule.varDeclarations ++ tlaModule.assumeDeclarations ++
      cinitDeclarations ++ initDeclarations ++ nextDeclarations ++ vcDeclarationsOrInvariants

    logger.info(s"  > Applying unique renaming")
    val outModule = incrementalRenaming.renameInModule(new TlaModule(tlaModule.name, newDecls))

    // print the resulting module
    writerFactory.writeModuleAllFormats(outModule.copy(name = "09_OutTransition"), TlaWriter.STANDARD_MODULES)

    Some(outModule)
  }

  private def extractTransitions(module: TlaModule, inOperName: String, outOperName: String): Seq[TlaOperDecl] = {
    val primedName = findBodyOf(inOperName, module.declarations: _*)
    val vars = module.varDeclarations.map(_.name)

    val sourceLoc = SourceLocator(sourceStore.makeSourceMap, changeListener)

    val operMap = BodyMapFactory.makeFromDecls(module.operDeclarations)
    val transitionPairs = SmtFreeSymbolicTransitionExtractor(tracker, sourceLoc)(vars.toSet, primedName, operMap)
    // sort the transitions by their identifiers, to make sure we have determinism
    val sortedTransitions = transitionPairs.map(_._2).sortBy(_.ID.id)
    ModuleAdapter.exprsToOperDefs(outOperName, sortedTransitions)
  }

  override def dependencies = Set(ModuleProperty.Primed, ModuleProperty.Preprocessed)

  override def transformations = Set(ModuleProperty.TransitionsFound)
}
