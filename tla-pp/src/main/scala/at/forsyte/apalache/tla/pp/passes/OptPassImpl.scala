package at.forsyte.apalache.tla.pp.passes

import java.io.File
import java.nio.file.Path
import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.{TlaModule, ModuleProperty}
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.pp.{ConstSimplifier, ExprOptimizer, UniqueNameGenerator}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * A preprocessing pass that simplifies TLA+ expression by running multiple transformation.
 *
 * @param options  pass options
 * @param gen      name generator
 * @param tracker  transformation tracker
 * @param nextPass next pass to call
 */
class OptPassImpl @Inject() (val options: PassOptions, gen: UniqueNameGenerator, tracker: TransformationTracker,
    writerFactory: TlaWriterFactory)
    extends OptPass with LazyLogging {

  override def name: String = "OptimizationPass"

  override def execute(module: TlaModule): Option[TlaModule] = {
    val transformationSequence =
      List(
          ConstSimplifier(tracker),
          ExprOptimizer(gen, tracker),
          ConstSimplifier(tracker),
      ) ///

    logger.info(" > Applying optimizations:")
    val optimized = transformationSequence.foldLeft(module) { case (m, tr) =>
      logger.info("  > %s".format(tr.getClass.getSimpleName))
      ModuleByExTransformer(tr).apply(m)
    }

    // dump the result of preprocessing
    writerFactory.writeModuleAllFormats(optimized.copy(name = "10_OutOpt"), TlaWriter.STANDARD_MODULES)

    Some(optimized)
  }

  override def dependencies = Set(ModuleProperty.Preprocessed)

  override def transformations = Set(ModuleProperty.Optimized)
}
