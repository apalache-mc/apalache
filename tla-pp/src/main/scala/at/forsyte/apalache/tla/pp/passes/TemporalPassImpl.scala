package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.pp.{TemporalEncoder, UniqueNameGenerator}
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
class TemporalPassImpl @Inject() (
    val options: PassOptions,
    tracker: TransformationTracker,
    gen: UniqueNameGenerator,
    writerFactory: TlaWriterFactory)
    extends TemporalPass with LazyLogging {

  override def name: String = "TemporalPass"

  override def execute(tlaModule: TlaModule): Option[TlaModule] = {
    logger.info("  > Rewriting temporal operators...")
    
    val newModule =
    options.get[List[String]]("checker", "inv") match {
      case Some(invariants) =>
        invariants.foldLeft(tlaModule) { (mod, invName) =>
            logger.info(s"  > Found invariant $invName")
            logger.info(s"  > Producing verification conditions from the invariant $invName")
            val optViewName = options.get[String]("checker", "view")
            if (optViewName.isDefined) {
              logger.info(s"  > Using state view ${optViewName.get}")
            }
            TemporalEncoder(gen).encode(mod, invName, optViewName)
          }
      case None =>
        logger.info("  > No temporal property given, nothing to rewrite")
        tlaModule
    }

    writeOut(writerFactory, newModule)

    Some(newModule)
  }

  override def dependencies = Set(ModuleProperty.TypeChecked)

  override def transformations = Set(ModuleProperty.TemporalEncoded)
}
