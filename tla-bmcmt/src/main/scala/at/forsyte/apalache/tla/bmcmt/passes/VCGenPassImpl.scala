package at.forsyte.apalache.tla.bmcmt.passes

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
    options: OptionGroup.HasCheckerPreds,
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory)
    extends VCGenPass with LazyLogging {

  override def name: String = "VCGen"

  override def execute(tlaModule: TlaModule): PassResult = {
    val newModule =
      options.predicates.invariants match {
        case List() =>
          val deadlockMsg = if (options.checker.noDeadlocks) "" else " Only deadlocks will be checked"
          logger.info(s"  > No invariant given.${deadlockMsg}")
          tlaModule
        case invariants =>
          invariants.foldLeft(tlaModule) { (mod, invName) =>
            logger.info(s"  > Producing verification conditions from the invariant $invName")
            val optView = options.predicates.view
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
