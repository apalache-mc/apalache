package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.bmcmt.VCGenerator
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.infra.passes.options.OptionGroup.WithCheckerPreds

/**
 * The pass that generates verification conditions.
 *
 * @author
 *   Igor Konnov
 */
class VCGenPassImpl @Inject() (
    checkerPreds: WithCheckerPreds,
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory)
    extends VCGenPass with LazyLogging {

  override def name: String = "VCGen"

  override def execute(tlaModule: TlaModule): PassResult = {
    val newModule =
      checkerPreds.predicates.invariants match {
        case List() =>
          val deadlockMsg = if (checkerPreds.checker.noDeadlocks) "" else " Only deadlocks will be checked"
          logger.info(s"  > No invariant given.${deadlockMsg}")
          tlaModule
        case invariants =>
          invariants.foldLeft(tlaModule) { (mod, invName) =>
            logger.info(s"  > Producing verification conditions from the invariant $invName")
            val optView = checkerPreds.predicates.view
            optView.foreach { viewName => logger.info(s"  > Using state view ${viewName}") }
            new VCGenerator(tracker).gen(mod, invName, optView)
          }
      }

    writeOut(writerFactory, newModule)

    Right(newModule)
  }

  override def dependencies = Set(ModuleProperty.Inlined)

  override def transformations = Set(ModuleProperty.VCGenerated)
}
