package at.forsyte.apalache.tla.passes.pp

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
import at.forsyte.apalache.infra.passes.DerivedPredicates

/**
 * The temporal pass takes a module with temporal properties, and outputs a module without temporal properties and an
 * invariant, such that if the invariant is never violated, then the original specification satisfies the temporal
 * formula. The encoding is described in https://lmcs.episciences.org/2236, Sections 3.2 and 4.
 */
class TemporalPassImpl @Inject() (
    derivedPreds: DerivedPredicates.Configurable,
    tracker: TransformationTracker,
    gen: UniqueNameGenerator,
    writerFactory: TlaWriterFactory,
    renaming: IncrementalRenaming)
    extends TemporalPass with LazyLogging {

  override def name: String = "TemporalPass"

  override def execute(tlaModule: TlaModule): PassResult = {
    logger.info("  > Rewriting temporal operators...")

    val temporalProps = derivedPreds.temporalProps
    val newModule = temporalProps match {
      case List() =>
        logger.info("  > No temporal property specified, nothing to encode")
        tlaModule
      case formulas =>
        temporalToInvariants(tlaModule, formulas)
    }

    writeOut(writerFactory, newModule)

    Right(newModule)
  }

  def temporalToInvariants(module: TlaModule, temporalProperties: List[String]): TlaModule = {
    val levelFinder = new TlaLevelFinder(module)

    val temporalFormulas = temporalProperties
      .map(propName => {
        module.declarations.find(_.name == propName)
      })
      .filter(propOption =>
        propOption match {
          case Some(temporalProp: TlaOperDecl) if temporalProp.formalParams.isEmpty =>
            val level = levelFinder.getLevelOfDecl(temporalProp)
            if (level != TlaLevelTemporal) {
              logger.warn(
                  s"  > Temporal property ${temporalProp.name} has no temporal operators, so it specifies a property of the initial state. Should ${temporalProp.name} be an invariant instead (--inv)?")
            }
            true
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
      val initDecl = module.declarations.find(_.name == derivedPreds.init).get.asInstanceOf[TlaOperDecl]
      val nextDecl = module.declarations.find(_.name == derivedPreds.next).get.asInstanceOf[TlaOperDecl]

      val loopEncoder = new LoopEncoder(tracker)

      val loopModWithPreds =
        loopEncoder.addLoopLogic(module, initDecl, nextDecl)

      // let-in expressions are hard to handle in temporal formulas,
      // so they are inlined here
      val inliner = new Inliner(tracker, renaming, keepNullaryMono = false)
      val transformation = inliner.transform(scope = Inliner.emptyScope)
      val inlinedTemporalFormulas =
        temporalFormulas.map(operDecl => operDecl.copy(body = transformation(operDecl.body)))

      // the encoding will transform the temporal properties into invariants, so add them to the
      // list of invariants (otherwise, they would not be treated as invariants by later passes)
      derivedPreds.addInvariants(inlinedTemporalFormulas.map(_.name))

      val tableauEncoder = new TableauEncoder(loopModWithPreds.module, gen, loopEncoder, tracker)
      tableauEncoder.temporalsToInvariants(loopModWithPreds, inlinedTemporalFormulas: _*)
    }
  }

  override def dependencies = Set(ModuleProperty.TypeChecked)

  override def transformations = Set(ModuleProperty.TemporalEncoded)
}
