package at.forsyte.apalache.tla.passes.pp

import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.tla.pp.{ConstSimplifier, ExprOptimizer, SetMembershipSimplifier, UniqueNameGenerator}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * A preprocessing pass that simplifies TLA+ expression by running multiple transformation.
 *
 * @param gen
 *   name generator
 * @param tracker
 *   transformation tracker
 * @param nextPass
 *   next pass to call
 */
class OptPassImpl @Inject() (
    gen: UniqueNameGenerator,
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory)
    extends OptPass with LazyLogging {

  override def name: String = "OptimizationPass"

  override def execute(module: TlaModule): PassResult = {
    val transformationSequence =
      List(
          ConstSimplifier(tracker),
          ExprOptimizer(gen, tracker),
          SetMembershipSimplifier(tracker),
          ConstSimplifier(tracker),
      ) ///

    logger.info(" > Applying optimizations:")
    val optimized = transformationSequence.foldLeft(module) { case (m, tr) =>
      logger.info("  > %s".format(tr.getClass.getSimpleName))
      ModuleByExTransformer(tr).apply(m)
    }

    // dump the result of preprocessing
    writeOut(writerFactory, optimized)

    Right(optimized)
  }

  override def dependencies = Set(ModuleProperty.Preprocessed)

  override def transformations = Set(ModuleProperty.Optimized)
}
