package at.forsyte.apalache.tla.bmcmt.passes

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
import at.forsyte.apalache.tla.assignments.SpecWithTransitions
import at.forsyte.apalache.tla.assignments.passes.SpecWithTransitionsMixin
import at.forsyte.apalache.tla.bmcmt.CheckerException
import at.forsyte.apalache.tla.bmcmt.analyses.{FormulaHintsStoreImpl, FreeExistentialsStoreImpl, HintFinder, SimpleSkolemization}
import at.forsyte.apalache.tla.lir.process.Renaming
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.io.PrettyWriter2
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * Find free-standing existential quantifiers and rename all local bindings, so they have unique names.
  *
  * @param options
  * @param frexStoreImpl
  * @param hintsStoreImpl
  * @param renaming
  * @param nextPass
  */
class HintsAndSkolemizationPassImpl @Inject()(val options: PassOptions,
                                              frexStoreImpl: FreeExistentialsStoreImpl,
                                              hintsStoreImpl: FormulaHintsStoreImpl,
                                              renaming: Renaming,
                                              @Named("AfterSkolem") nextPass: Pass with SpecWithTransitionsMixin)
  extends HintsAndSkolemizationPass with LazyLogging {

  private var specWithTransitions: Option[SpecWithTransitions] = None

  /**
    * The pass name.
    *
    * @return the name associated with the pass
    */
  override def name: String = "SkolemizationAndHints"

  object StringOrdering extends Ordering[Object] {
    override def compare(x: Object, y: Object): Int = x.toString compare y.toString
  }

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
    // Rename bound variables, so each of them is unique. This is required by TrivialTypeFinder.
    // Hint by Markus Kuppe: sort init and next to get a stable ordering between the runs.
    // The most stable way is to sort them by their string representation.
    val initRenamed = spec.initTransitions.sorted(StringOrdering).map(renaming.renameBindingsUnique)
    val nextRenamed = spec.nextTransitions.sorted(StringOrdering).map(renaming.renameBindingsUnique)

    def renameIfDefined(ex: Option[TlaEx]): Option[TlaEx] = ex match {
      case Some(ni) => Some(renaming.renameBindingsUnique(ni))
      case None => None
    }

    val constInitPrimeRenamed = renameIfDefined(spec.constInitPrime)
    val notInvRenamed = renameIfDefined(spec.notInvariant)
    val notInvPrimeRenamed = renameIfDefined(spec.notInvariantPrime)
    var newSpec = new SpecWithTransitions(spec.rootModule, initRenamed, nextRenamed,
      constInitPrimeRenamed, notInvRenamed, notInvPrimeRenamed)
    val skolem = new SimpleSkolemization(frexStoreImpl)
    newSpec = skolem.transformAndLabel(newSpec)

    logger.debug("Transitions after renaming and skolemization")
    for ((t, i) <- newSpec.initTransitions.zipWithIndex) {
      val stringWriter = new StringWriter()
      new PrettyWriter2(new PrintWriter(stringWriter)).write(t)
      logger.debug("Initial transition #%d:\n%s".format(i, stringWriter.toString))
    }
    for ((t, i) <- newSpec.nextTransitions.zipWithIndex) {
      val stringWriter = new StringWriter()
      new PrettyWriter2(new PrintWriter(stringWriter)).write(t)
      logger.debug("Next transition #%d:\n   %s".format(i, stringWriter.toString))
    }
    logger.debug("Negated invariant:\n   %s".format(newSpec.notInvariant))

    val hintFinder = new HintFinder(hintsStoreImpl)
    hintFinder.findHints(spec)

    nextPass.setSpecWithTransitions(newSpec)
    val nfree = frexStoreImpl.store.size
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
