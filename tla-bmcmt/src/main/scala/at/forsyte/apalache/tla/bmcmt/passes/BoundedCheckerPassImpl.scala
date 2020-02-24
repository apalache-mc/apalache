package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
import at.forsyte.apalache.tla.assignments.ModuleAdapter
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, FormulaHintsStore}
import at.forsyte.apalache.tla.bmcmt.search.{BfsStrategy, BfsStrategyStopWatchDecorator, DfsStrategy}
import at.forsyte.apalache.tla.bmcmt.types.{CellT, TypeFinder}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.NullEx
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.LanguageWatchdog
import at.forsyte.apalache.tla.lir.transformations.standard.KeraLanguagePred
import at.forsyte.apalache.tla.pp.NormalizedNames
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
      throw new CheckerException(s"The input of $name pass is not initialized", NullEx)
    }
    val module = tlaModule.get

    for (decl <- module.operDeclarations) {
      LanguageWatchdog(KeraLanguagePred()).check(decl.body)
    }

    val initTrans = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.INIT_PREFIX)
    val nextTrans = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.NEXT_PREFIX)
    val cinitP = ModuleAdapter.getOperatorOption(module, NormalizedNames.CONST_INIT)
    val vcInvs = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.VC_INV_PREFIX)
    val vcNotInvs = ModuleAdapter.getTransitionsFromSpec(module, NormalizedNames.VC_NOT_INV_PREFIX)
    val invariantsAndNegations = vcInvs.zip(vcNotInvs)

    val input = new CheckerInput(module, initTrans.toList, nextTrans.toList, cinitP, invariantsAndNegations.toList)
    val stepsBound = options.getOrElse("checker", "length", 10)
    val debug = options.getOrElse("general", "debug", false)
    val profile = options.getOrElse("smt", "prof", false)
    val search = options.getOrElse("checker", "search", "dfs")
    val tuning = options.getOrElse("general", "tuning", Map[String, String]())
    val checkRuntime = false // deprecated, will be removed in 0.7.0
    val strategy =
      if (search == "bfs") {
        new BfsStrategyStopWatchDecorator(new BfsStrategy(input, stepsBound), filename="bfs.csv")
      } else {
        val random = tuning.getOrElse("search.randomDfs", "")
        new DfsStrategy(input, stepsBound, random.toLowerCase.equals("true"))
      }
    val tlc = options.getOrElse("checker", "tlc", false)

    val checker: Checker =
        new ModelChecker(typeFinder, hintsStore, changeListener, exprGradeStore, sourceStore,
          input, strategy, tuning, debug, profile, checkRuntime, tlc)

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
