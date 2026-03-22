package at.forsyte.apalache.tla.passes.assignments

import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.assignments._
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.storage.{BodyMapFactory, ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.pp.NormalizedNames
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.DerivedPredicates
import at.forsyte.apalache.tla.types.tla

/**
 * This pass finds symbolic transitions in Init and Next.
 */
class TransitionPassImpl @Inject() (
    derivedPreds: DerivedPredicates,
    sourceStore: SourceStore,
    tracker: TransformationTracker,
    changeListener: ChangeListener,
    incrementalRenaming: IncrementalRenaming,
    writerFactory: TlaWriterFactory)
    extends TransitionPass with LazyLogging {

  override def name: String = "TransitionFinderPass"

  override def execute(tlaModule: TlaModule): PassResult = {

    val vars = tlaModule.varDeclarations.map(_.name).toSet
    val sourceLoc = SourceLocator(sourceStore.makeSourceMap, changeListener)
    val operDecls = tlaModule.operDeclarations
    val operMap = BodyMapFactory.makeFromDecls(operDecls)

    def extractTransitions(varSet: Set[String], inOperName: String, outOperName: String): Seq[TlaOperDecl] = {
      val primedName = findBodyOf(inOperName, operDecls: _*)
      val transitionPairs = SmtFreeSymbolicTransitionExtractor(tracker, sourceLoc)(varSet, primedName, operMap)
      // sort the transitions by their identifiers, to make sure we have determinism
      val sortedTransitions = transitionPairs.map(_._2).sortBy(_.ID.id)
      ModuleAdapter.exprsToOperDefs(outOperName, sortedTransitions)
    }

    // extract transitions from InitPrimed
    val initOperName = derivedPreds.init
    val initOperNamePrimed = initOperName + "Primed"
    val initDeclarations = extractTransitions(vars, initOperNamePrimed, NormalizedNames.INIT_PREFIX)
    logger.info(s"  > Found ${initDeclarations.size} initializing transitions")

    // extract transitions from Next
    val nextOperName = derivedPreds.next
    val nextDeclarations = extractTransitions(vars, nextOperName, NormalizedNames.NEXT_PREFIX)
    logger.info(s"  > Found ${nextDeclarations.size} transitions")

    val invDeclarations: Seq[TlaDecl] = derivedPreds.invariants.map { invariant =>
      tlaModule.declarations.find(_.name == invariant).get
    }

    // convert an optional CInit operator
    val cinitDeclarations =
      derivedPreds.cinit match {
        case None =>
          logger.info(s"  > No constant initializer")
          Seq()

        case Some(cinitName) =>
          logger.info(s"  > Found constant initializer $cinitName")
          val cinitTransitions =
            extractTransitions(
                tlaModule.constDeclarations.map { _.name }.toSet, // "vars" for cinit are constants
                cinitName + "Primed",
                "", // outName doesn't matter, we're merging them
            )
          val cinitMonolyth: TlaEx = tla.and(cinitTransitions.map { d => tla.unchecked(d.body) }: _*)
          Seq(ModuleAdapter.exprToOperDef(NormalizedNames.CONST_INIT, cinitMonolyth))
      }

    // Add the constants, variables, and assumptions; then add CInit, Init*, Next*; then add verification conditions.
    val vcDeclarations = tlaModule.declarations.filter(NormalizedNames.isVC)
    // In case verification conditions weren't generated yet, keep the raw invariants
    val vcDeclarationsOrInvariants = if (vcDeclarations.isEmpty) invDeclarations else vcDeclarations
    // Remember to add persistent operators, if any
    val persistentDecls = tlaModule.declarations.filter(d => derivedPreds.persistent.contains(d.name))

    val newDecls = tlaModule.constDeclarations ++ tlaModule.varDeclarations ++ tlaModule.assumeDeclarations ++
      cinitDeclarations ++ initDeclarations ++ nextDeclarations ++ vcDeclarationsOrInvariants ++ persistentDecls

    logger.info(s"  > Applying unique renaming")
    val outModule = incrementalRenaming.renameInModule(new TlaModule(tlaModule.name, newDecls))

    // print the resulting module
    writeOut(writerFactory, outModule)

    Right(outModule)
  }

  override def dependencies = Set(ModuleProperty.Primed, ModuleProperty.Preprocessed)

  override def transformations = Set(ModuleProperty.TransitionsFound)
}
