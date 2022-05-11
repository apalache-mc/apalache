package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.pp.{TemporalEncoder, UniqueNameGenerator}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.TlaLevelFinder

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
class TemporalPassImpl @Inject() (
    val options: PassOptions,
    gen: UniqueNameGenerator,
    writerFactory: TlaWriterFactory)
    extends TemporalPass with LazyLogging {

  override def name: String = "TemporalPass"

  override def execute(tlaModule: TlaModule): Option[TlaModule] = {
    logger.info("  > Rewriting temporal operators...")

    val newModule = options.get[List[String]]("checker", "inv") match {
      case None =>
        logger.info("  > No invariants specified, nothing to encode")
        tlaModule
      case Some(invariants) =>
        val init = options.get[String]("checker", "init")
        if (init.isEmpty){
          logger.info("  > `init` is not set, cannot encode invariants")
          None
        }
        val next = options.get[String]("checker", "next")
        if (init.isEmpty){
          logger.info("  > `next` is not set, cannot encode invariants")
          None
        }
        new TemporalEncoder(tlaModule, gen).encodeInvariants(invariants, init.get, next.get)
    }

    writeOut(writerFactory, newModule)

    Some(newModule)
  }

  override def dependencies = Set(ModuleProperty.TypeChecked)

  override def transformations = Set(ModuleProperty.TemporalEncoded)
}
