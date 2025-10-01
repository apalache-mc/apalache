package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.DerivedPredicates
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.tla.bmcmt.VCGenerator
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
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
    derivedPredicates: DerivedPredicates,
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
