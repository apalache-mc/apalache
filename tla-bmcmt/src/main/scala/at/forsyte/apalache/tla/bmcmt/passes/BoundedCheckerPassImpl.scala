package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
import at.forsyte.apalache.tla.assignments.SpecWithTransitions
import at.forsyte.apalache.tla.bmcmt.Checker.Outcome
import at.forsyte.apalache.tla.bmcmt.{Checker, CheckerException, CheckerInput}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * The implementation of a bounded model checker with SMT.
  *
  * @author Igor Konnov
  */
class BoundedCheckerPassImpl @Inject() (val options: PassOptions,
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
      throw new CheckerException("The input of BoundedChecker pass is not initialized")
    }
    val spec = specWithTransitions.get
    // TODO: add the invariant
    val input = new CheckerInput(spec.rootModule, spec.initTransitions, spec.nextTransitions, invariant = None)
    val stepsBound = options.getOption("checker", "length", 10).asInstanceOf[Int]
    val outcome = new Checker(input, stepsBound).run()
    logger.info("The outcome is: " + outcome)
    outcome == Outcome.NoError
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
