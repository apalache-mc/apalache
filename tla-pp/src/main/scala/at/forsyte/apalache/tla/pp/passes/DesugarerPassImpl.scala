package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.pp.{Desugarer, UniqueNameGenerator}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * Desugarer pass.
 *
 * @param options
 *   pass options
 * @param tracker
 *   transformation tracker
 * @param nextPass
 *   next pass to call
 */
class DesugarerPassImpl @Inject() (
    val options: PassOptions,
    tracker: TransformationTracker,
    gen: UniqueNameGenerator,
    writerFactory: TlaWriterFactory)
    extends DesugarerPass with LazyLogging {

  override def name: String = "DesugarerPass"

  override def execute(tlaModule: TlaModule): PassResult = {
    logger.info("  > Desugaring...")
    val input = tlaModule
    val varNames = input.varDeclarations.map {
      _.name
    }.toSet
    val output = ModuleByExTransformer(Desugarer(gen, varNames, tracker))(input)

    // dump the result of preprocessing
    writeOut(writerFactory, output)
    Right(output)
  }

  override def dependencies = Set(ModuleProperty.TypeChecked)

  override def transformations = Set(ModuleProperty.Desugared)
}
