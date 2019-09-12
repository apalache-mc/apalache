package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
import at.forsyte.apalache.tla.assignments.ModuleManipulator
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, FormulaHintsStore, FreeExistentialsStoreImpl}
import at.forsyte.apalache.tla.bmcmt.search.{BfsStrategy, BfsStrategyStopWatchDecorator, DfsStrategy}
import at.forsyte.apalache.tla.bmcmt.types.{CellT, TypeFinder}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.storage.ChangeListener
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
                                        freeExistentialsStore: FreeExistentialsStoreImpl,
                                        hintsStore: FormulaHintsStore,
                                        exprGradeStore: ExprGradeStore,
                                        sourceStore: SourceStore,
                                        changeListener: ChangeListener,
                                        @Named("AfterChecker") nextPass: Pass)
      extends BoundedCheckerPass with LazyLogging {

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
    if (tlaModule.isEmpty) {
      throw new CheckerException(s"The input of $name pass is not initialized")
    }
    val module = tlaModule.get

    import at.forsyte.apalache.tla.assignments.ModuleManipulator.defaultNames._

    val initTrans = ModuleManipulator.getTransitionsFromSpec( module, s"$renamingPrefix$initDefaultName" )
    val nextTrans = ModuleManipulator.getTransitionsFromSpec( module, s"$renamingPrefix$nextDefaultName" )
    val cinitP = ModuleManipulator.getOperatorOption( module, s"$renamingPrefix$cinitDefaultName" )
    val notInvP = ModuleManipulator.getOperatorOption( module, s"$renamingPrefix$notInvPrimeDefaultName" )

    val input = new CheckerInput(module, initTrans.toList, nextTrans.toList, cinitP, notInvP)
    val stepsBound = options.getOption("checker", "length", 10).asInstanceOf[Int]
    val debug = options.getOption("general", "debug", false).asInstanceOf[Boolean]
    val profile = options.getOption("smt", "prof", false).asInstanceOf[Boolean]
    val search = options.getOption("checker", "search", "dfs").asInstanceOf[String]
    val tuning = options.getOption("general", "tuning", default = Map[String, String]())
      .asInstanceOf[Map[String, String]]
    val checkRuntime =
      options.getOption("checker", "checkRuntime", false).asInstanceOf[Boolean]
    val strategy =
      if (search == "bfs") {
        new BfsStrategyStopWatchDecorator(new BfsStrategy(input, stepsBound), filename="bfs.csv")
      } else {
        val random = tuning.getOrElse("search.randomDfs", "")
        new DfsStrategy(input, stepsBound, random.toLowerCase.equals("true"))
      }

    val checker: Checker =
        new ModelChecker(typeFinder, freeExistentialsStore, hintsStore, changeListener, exprGradeStore, sourceStore,
          input, strategy, tuning, debug, profile, checkRuntime)

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
  override def next(): Option[Pass] =
    tlaModule map {_ => nextPass}
}
