package at.forsyte.apalache.tla.passes.pp

import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule, TlaOperDecl}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.pp.{Desugarer, UniqueNameGenerator}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * Desugarer pass.
 *
 * @param tracker
 *   transformation tracker
 * @param nextPass
 *   next pass to call
 */
class DesugarerPassImpl @Inject() (
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
    // Collect nullary operator definitions so the Desugarer can expand operator
    // references inside UNCHANGED (e.g., UNCHANGED vars where vars == <<myList1, myList2>>).
    // See: https://github.com/apalache-mc/apalache/issues/3143
    val operDefs = input.operDeclarations.collect {
      case TlaOperDecl(name, params, body) if params.isEmpty => name -> body
    }.toMap
    val output = ModuleByExTransformer(Desugarer(gen, varNames, tracker, operDefs))(input)

    // dump the result of preprocessing
    writeOut(writerFactory, output)
    Right(output)
  }

  override def dependencies = Set(ModuleProperty.TypeChecked)

  override def transformations = Set(ModuleProperty.Desugared)
}
