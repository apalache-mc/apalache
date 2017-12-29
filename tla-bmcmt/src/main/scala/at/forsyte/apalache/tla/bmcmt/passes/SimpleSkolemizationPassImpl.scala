package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
import at.forsyte.apalache.tla.assignments.SpecWithTransitions
import at.forsyte.apalache.tla.assignments.passes.SpecWithTransitionsMixin
import at.forsyte.apalache.tla.bmcmt.CheckerException
import at.forsyte.apalache.tla.bmcmt.analyses.{FreeExistentialsStoreImpl, SimpleSkolemization}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

class SimpleSkolemizationPassImpl @Inject()(val options: PassOptions,
                                            freeExistentialsStoreImpl: FreeExistentialsStoreImpl,
                                            @Named("AfterSkolem") nextPass: Pass with SpecWithTransitionsMixin)
  extends SimpleSkolemizationPass with LazyLogging {

  private var specWithTransitions: Option[SpecWithTransitions] = None

  /**
    * The pass name.
    *
    * @return the name associated with the pass
    */
  override def name: String = "SimpleSkolemization"

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
    val skolem = new SimpleSkolemization(freeExistentialsStoreImpl)
    val newSpec = skolem.transformAndLabel(spec)
    nextPass.setSpecWithTransitions(newSpec)
    val nfree = freeExistentialsStoreImpl.store.size
    logger.info(s"Found $nfree free existentials in the transitions")
    true
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    Some(nextPass)
  }

  override def setSpecWithTransitions(spec: SpecWithTransitions): Unit = {
    specWithTransitions = Some(spec)
  }
}
