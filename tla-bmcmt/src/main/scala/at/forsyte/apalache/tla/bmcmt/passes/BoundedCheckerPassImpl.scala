package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
import at.forsyte.apalache.tla.assignments.SpecWithTransitions
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, FreeExistentialsStore}
import at.forsyte.apalache.tla.bmcmt.types.{CellT, TypeFinder}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.IdOrdering
import at.forsyte.apalache.tla.lir.process.Renaming
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * The implementation of a bounded model checker with SMT.
  *
  * @author Igor Konnov
  */
class BoundedCheckerPassImpl @Inject() (val options: PassOptions,
                                        typeFinder: TypeFinder[CellT],
                                        freeExistentialsStore: FreeExistentialsStore,
                                        exprGradeStore: ExprGradeStore,
                                        sourceStore: SourceStore,
                                        renaming: Renaming,
                                        @Named("AfterChecker") nextPass: Pass)
      extends BoundedCheckerPass with LazyLogging {

  private var specWithTransitions: Option[SpecWithTransitions] = None

  /**
    * The pass name.
    *
    * @return the name associated with the pass
    */
  override def name: String = "BoundedChecker"

  /**
    * Run the pass.
    *
    * @return true, if the pass was successful
    */
  override def execute(): Boolean = {
    if (specWithTransitions.isEmpty) {
      throw new CheckerException(s"The input of $name pass is not initialized")
    }
    val spec = specWithTransitions.get
    // rename bound variables, so each of them is unique. This is required by TrivialTypeFinder.
    // hint by Markus Kuppe: sort init and next to get a stable ordering between the runs
    val initSorted = spec.initTransitions.map(renaming.renameBindingsUnique).sorted(IdOrdering)
    val nextSorted = spec.nextTransitions.map(renaming.renameBindingsUnique).sorted(IdOrdering)
    val notInvariantNew =
      if (spec.notInvariant.isDefined) Some(renaming.renameBindingsUnique(spec.notInvariant.get)) else None

    logger.debug("Transitions after renamed")
    for ((t, i) <- initSorted.zipWithIndex) {
      logger.debug("Initial transition #%d:\n   %s".format(i, t))
    }
    for ((t, i) <- nextSorted.zipWithIndex) {
      logger.debug("Next transition #%d:\n   %s".format(i, t))
    }
    logger.debug("Negated invariant:\n   %s".format(notInvariantNew))

    val input = new CheckerInput(spec.rootModule, initSorted, nextSorted, notInvariantNew)
    val stepsBound = options.getOption("checker", "length", 10).asInstanceOf[Int]
    val debug = options.getOption("general", "debug", false).asInstanceOf[Boolean]
    val profile = options.getOption("smt", "prof", false).asInstanceOf[Boolean]
    val search = options.getOption("checker", "search", "dfs").asInstanceOf[String]
    val checker: Checker =
      if (search == "dfs") {
        new DfsChecker(typeFinder, freeExistentialsStore, input, stepsBound, debug)
      } else {
        new BfsChecker(typeFinder, freeExistentialsStore, exprGradeStore,
          sourceStore, input, stepsBound, debug, profile)
      }
    val outcome = checker.run()
    logger.info("The outcome is: " + outcome)
    outcome == Checker.Outcome.NoError
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    if (specWithTransitions.isDefined) {
      Some(nextPass)
    } else {
      None
    }
  }

  override def setSpecWithTransitions(spec: SpecWithTransitions): Unit = {
    specWithTransitions = Some(spec)
  }
}
