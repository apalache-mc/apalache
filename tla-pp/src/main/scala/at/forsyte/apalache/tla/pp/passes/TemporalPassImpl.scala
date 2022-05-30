package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.pp.temporal.{LoopEncoder, TableauEncoder}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.pp.TlaInputError
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.infra.passes.WriteablePassOptions

/**
 * The temporal pass takes a module with temporal properties, and outputs a module without temporal properties and an
 * invariant, such that if the invariant is never violated, then the original specification satisfies the temporal
 * formula. The encoding is described in https://lmcs.episciences.org/2236, Sections 3.2 and 4.
 */
class TemporalPassImpl @Inject() (
    val options: WriteablePassOptions,
    tracker: TransformationTracker,
    gen: UniqueNameGenerator,
    writerFactory: TlaWriterFactory)
    extends TemporalPass with LazyLogging {

  override def name: String = "TemporalPass"

  override def execute(tlaModule: TlaModule): PassResult = {
    logger.info("  > Rewriting temporal operators...")

    val temporalProps = options.get[List[String]]("checker", "temporal")
    val newModule = temporalProps match {
      case None =>
        logger.info("  > No formula specified, nothing to encode")
        tlaModule
      case Some(formula) =>
        val init = options.get[String]("checker", "init")
        if (init.isEmpty) {
          logger.info("  > `init` is not set, cannot encode formula")
          None
        }
        val next = options.get[String]("checker", "next")
        if (init.isEmpty) {
          logger.info("  > `next` is not set, cannot encode formula")
          None
        }
        // formula will be transformed into an invariant, so it is added as an invariant to check
        options.set("checker.inv", options.get("checker", "inv") ++ formula)
        encodeFormula(tlaModule, formula, init.get, next.get)
    }

    writeOut(writerFactory, newModule)

    Right(newModule)
  }

  def encodeFormula(
      module: TlaModule,
      formulas: List[String],
      init: String,
      next: String): TlaModule = {
    val levelFinder = new TlaLevelFinder(module)

    val temporalFormulas = formulas
      .map(invName => {
        module.declarations.find(_.name == invName)
      })
      .filter(invOption =>
        invOption match {
          case Some(inv: TlaOperDecl) if inv.formalParams.isEmpty =>
            val level = levelFinder.getLevelOfDecl(inv)
            if (level != TlaLevelTemporal) {
              logger.warn(
                  s"  > Temporal property ${inv.name} has no temporal operators, so it specifies a property of the initial state. Should ${inv.name} be an invariant instead (--inv)?")
            }
            true
          case _ => false
        })
      .map(invOption => invOption.get.asInstanceOf[TlaOperDecl])

    if (temporalFormulas.isEmpty) {
      logger.info("  > No temporal properties found, nothing to encode")
      module
    } else {
      logger.info(s"  > Found ${temporalFormulas.length} temporal properties")
      logger.info(s"  > Adding logic for loop finding")

      val initDecl = module.declarations.find(_.name == init) match {
        case Some(initDecl: TlaOperDecl) =>
          val nparams = initDecl.formalParams.length
          if (nparams != 0) {
            val message =
              s"Expected init predicate $init to have 0 params, found $nparams parameters"
            throw new TlaInputError(message, Some(initDecl.body.ID))
          }
          initDecl
        case None =>
          val message = (s"init predicate named `${init}` not found")
          throw new TlaInputError(message)
        case _ =>
          val message = (s"Expected to find a predicate named `${init}` but did not")
          throw new TlaInputError(message)
      }

      val nextDecl = module.declarations.find(_.name == next) match {
        case Some(nextDecl: TlaOperDecl) =>
          val nparams = nextDecl.formalParams.length
          if (nparams != 0) {
            val message =
              s"Expected next predicate $init to have 0 params, found $nparams parameters"
            throw new TlaInputError(message, Some(nextDecl.body.ID))
          }
          nextDecl
        case None =>
          val message = (s"next predicate named `${init}` not found")
          throw new TlaInputError(message)
        case _ =>
          val message = (s"Expected to find a predicate named `${init}` but did not")
          throw new TlaInputError(message)
      }

      val loopEncoder = new LoopEncoder(tracker)

      val loopModWithPreds =
        loopEncoder.addLoopLogic(module, initDecl, nextDecl)

      val tableauEncoder = new TableauEncoder(loopModWithPreds.module, gen, loopEncoder, tracker)
      val tableauModWithPreds = tableauEncoder.encodeFormulas(loopModWithPreds, temporalFormulas)

      tableauModWithPreds.module
    }
  }

  override def dependencies = Set(ModuleProperty.TypeChecked)

  override def transformations = Set(ModuleProperty.TemporalEncoded)
}
