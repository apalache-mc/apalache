package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.pp.temporal.{LoopEncoder, TableauEncoder}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.pp.Inliner
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming

/**
 * The temporal pass takes a module with temporal properties, and outputs a module without temporal properties and an
 * invariant, such that if the invariant is never violated, then the original specification satisfies the temporal
 * formula. The encoding is described in https://lmcs.episciences.org/2236, Sections 3.2 and 4.
 */
class TemporalPassImpl @Inject() (
    val options: PassOptions,
    tracker: TransformationTracker,
    gen: UniqueNameGenerator,
    writerFactory: TlaWriterFactory,
    renaming: IncrementalRenaming)
    extends TemporalPass with LazyLogging {

  override def name: String = "TemporalPass"

  override def execute(tlaModule: TlaModule): PassResult = {
    logger.info("  > Rewriting temporal operators...")

    val newModule = options.get[List[String]]("checker", "inv") match {
      case None =>
        logger.info("  > No invariants specified, nothing to encode")
        tlaModule
      case Some(invariants) =>
        val init = options.get[String]("checker", "init")
        val next = options.get[String]("checker", "next")
        temporalToInvariants(tlaModule, invariants, init.get, next.get)
    }

    writeOut(writerFactory, newModule)

    Right(newModule)
  }

  def temporalToInvariants(
      module: TlaModule,
      temporalProperties: List[String],
      init: String,
      next: String): TlaModule = {
    val levelFinder = new TlaLevelFinder(module)

    val temporalFormulas = temporalProperties
      .map(propName => {
        module.declarations.find(_.name == propName)
      })
      .filter(propOption =>
        propOption match {
          case Some(inv: TlaOperDecl) if inv.formalParams.isEmpty =>
            val level = levelFinder.getLevelOfDecl(inv)
            level == TlaLevelTemporal
          case _ => false
        })
      .map(propOption => propOption.get.asInstanceOf[TlaOperDecl])

    if (temporalFormulas.isEmpty) {
      logger.info("  > No temporal properties found, nothing to encode")
      module
    } else {
      logger.info(s"  > Found ${temporalFormulas.length} temporal properties")
      logger.info(s"  > Adding logic for loop finding")

      // if init and next don't exist, Apalache should throw already in an earlier pass
      // so it's safe to assume they exist
      val initDecl = module.declarations.find(_.name == init).get.asInstanceOf[TlaOperDecl]
      val nextDecl = module.declarations.find(_.name == next).get.asInstanceOf[TlaOperDecl]

      val loopEncoder = new LoopEncoder(tracker)

      val loopModWithPreds =
        loopEncoder.addLoopLogic(module, initDecl, nextDecl)

      // let-in expressions are hard to handle in temporal formulas,
      // so they are inlined here
      val inliner = new Inliner(tracker, renaming, keepNullary = false)
      val transformation = inliner.transform(scope = Inliner.emptyScope)
      val inlinedTemporalFormulas =
        temporalFormulas.map(operDecl => operDecl.copy(body = transformation(operDecl.body)))

      val tableauEncoder = new TableauEncoder(loopModWithPreds.module, gen, loopEncoder, tracker)
      tableauEncoder.temporalsToInvariants(loopModWithPreds, inlinedTemporalFormulas: _*)
    }
  }

  override def dependencies = Set(ModuleProperty.TypeChecked)

  override def transformations = Set(ModuleProperty.TemporalEncoded)
}
