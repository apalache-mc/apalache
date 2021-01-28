package at.forsyte.apalache.tla.pp.passes

import java.io.File
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.pp.{ConstSimplifier, ExprOptimizer, UniqueNameGenerator}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * A preprocessing pass that simplifies TLA+ expression by running multiple transformation.
  * @param options pass options
  * @param gen name generator
  * @param tracker transformation tracker
  * @param nextPass next pass to call
  */
class OptPassImpl @Inject()(val options: PassOptions,
                            gen: UniqueNameGenerator,
                            renaming: IncrementalRenaming,
                            tracker: TransformationTracker,
                            @Named("AfterOpt") nextPass: Pass with TlaModuleMixin)
    extends OptPass with LazyLogging {

  private var outputTlaModule: Option[TlaModule] = None

  /**
    * The pass name.
    *
    * @return the name associated with the pass
    */
  override def name: String = "OptimizationPass"

  /**
    * Run the pass.
    *
    * @return true, if the pass was successful
    */
  override def execute(): Boolean = {
    val module = tlaModule.get

    val transformationSequence =
      List(
        ConstSimplifier(tracker),
        ExprOptimizer(gen, tracker),
        ConstSimplifier(tracker)
      ) ///

    logger.info(" > Applying optimizations:")
    val optimized = transformationSequence.foldLeft(module) {
      case (m, tr) =>
        logger.info("  > %s".format(tr.getClass.getSimpleName))
        ModuleByExTransformer(tr).apply(m)
    }

    // dump the result of preprocessing
    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    PrettyWriter.write(optimized, new File(outdir.toFile, "out-opt.tla"))

    outputTlaModule = Some(optimized)
    true
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    outputTlaModule map { m =>
      nextPass.setModule( m )
      nextPass
    }
  }
}
