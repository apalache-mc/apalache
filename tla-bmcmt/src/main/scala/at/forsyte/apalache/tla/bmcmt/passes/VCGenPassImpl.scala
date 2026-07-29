package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.DerivedPredicates
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.tla.bmcmt.VCGenerator
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * The pass that generates verification conditions.
 *
 * @author
 *   Igor Konnov
 */
class VCGenPassImpl @Inject() (
    options: OptionGroup.HasChecker,
    derivedPredicates: DerivedPredicates.Configurable,
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory)
    extends VCGenPass with LazyLogging {

  override def name: String = "VCGen"

  override def execute(tlaModule: TlaModule): PassResult = {
    val moduleWithInvariants =
      derivedPredicates.invariants match {
        case List() =>
          val deadlockMsg = if (options.checker.noDeadlocks) "" else " Only deadlocks will be checked"
          logger.info(s"  > No invariant given.$deadlockMsg")
          tlaModule
        case invariants =>
          invariants.foldLeft(tlaModule) { (mod, invName) =>
            logger.info(s"  > Producing verification conditions from the invariant $invName")
            new VCGenerator(tracker).genInv(mod, invName)
          }
      }

    // The invariants that are conjuncts of the init predicate hold in the initial states by construction. We pass them
    // on to the model checker, which then does not check them in state 0, see #1825. The expressions that we build on
    // the way are only used for comparison, hence the idle tracker.
    val impliedByInit =
      new VCGenerator(new IdleTracker).findInvariantsImpliedByInit(moduleWithInvariants, derivedPredicates.init)
    if (impliedByInit.nonEmpty) {
      val nConditions = impliedByInit.length
      logger.info(s"  > $nConditions verification condition(s) follow from ${derivedPredicates.init}")
    }
    derivedPredicates.setInvariantsImpliedByInit(impliedByInit.toList)

    val moduleWithInvariantsAndView =
      derivedPredicates.view
        .map(viewName => {
          logger.info(s"  > Using state view $viewName")
          new VCGenerator(tracker).genView(moduleWithInvariants, viewName)
        })
        .getOrElse(moduleWithInvariants)

    writeOut(writerFactory, moduleWithInvariantsAndView)

    Right(moduleWithInvariantsAndView)
  }

  override def dependencies = Set(ModuleProperty.Inlined)

  override def transformations = Set(ModuleProperty.VCGenerated)
}
