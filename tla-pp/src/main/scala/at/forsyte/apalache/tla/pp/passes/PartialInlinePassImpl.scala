package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.lir.storage.{BodyMap, BodyMapFactory}
import at.forsyte.apalache.tla.lir.transformations._
import at.forsyte.apalache.tla.lir.transformations.standard.ModuleByExTransformer
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule, TlaOperDecl}
import at.forsyte.apalache.tla.pp._
import com.typesafe.scalalogging.LazyLogging

/**
 * A pass that expands operators and let-in definitions.
 */
abstract class PartialInlinePassImpl(
    val options: PassOptions,
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory)
    extends InlinePass with LazyLogging {

  override def name: String = "InlinePass"

  val transformationSequence: List[BodyMap => TlaExTransformation]

  override def execute(module: TlaModule): Option[TlaModule] = {
    val inlined = transformationSequence.foldLeft(module) { case (m, trBuilder) =>
      val operMap = BodyMapFactory.makeFromDecls(m.operDeclarations)
      val tr = trBuilder(operMap)
      logger.info("  > %s".format(tr.getClass.getSimpleName))
      ModuleByExTransformer(tr)(m)
    }

    // Since PrimingPass now happens before inlining, we have to add InitPrime and CInitPrime as well
    val initName = options.getOrElse[String]("checker", "init", "Init")
    val cinitName = options.getOrElse[String]("checker", "cinit", "CInit")
    val initPrimedName = initName + "Primed"
    val cinitPrimedName = cinitName + "Primed"

    // Inline the primitive constants now
    val constants = module.constDeclarations.map { _.name }
    val cInitBody = findBodyOf(cinitName, inlined.declarations: _*)
    val constInliner = TlaConstInliner(tracker, constants.toSet)
    val constMap = constInliner.buildConstMap(Map.empty)(cInitBody)
    val declTr: TlaDeclTransformation = tracker.trackDecl {
      // When inlining, we keep the original CInit(Primed)
      case d @ TlaOperDecl(name, _, body) if (name != cinitName && name != cinitPrimedName) =>
        d.copy(body = constInliner.replaceConstWithValue(constMap)(body))(d.typeTag)
      case d => d // keep the rest as they are
    }
    val constInlinedModule = inlined.copy(
        declarations = inlined.declarations.map(declTr)
    )

    // Fixing issue 283: https://github.com/informalsystems/apalache/issues/283
    // Remove the operators that are not needed,
    // as some of them may contain higher-order operators that cannot be substituted
    val relevantOperators = NormalizedNames.userOperatorNamesFromOptions(options).toSet
    val relevantOperatorsAndInitCInitPrimed = relevantOperators + initPrimedName + cinitPrimedName

    logger.info("Leaving only relevant operators: " + relevantOperatorsAndInitCInitPrimed.toList.sorted.mkString(", "))
    val filteredDefs = constInlinedModule.declarations.filter {
      case TlaOperDecl(name, _, _) =>
        relevantOperatorsAndInitCInitPrimed.contains(name)
      case _ => true // accept all other declarations
    }

    val filtered = constInlinedModule.copy(
        declarations = filteredDefs
    )

    // dump the result of preprocessing
    writerFactory.writeModuleAllFormats(filtered.copy(name = "05_OutInline"), TlaWriter.STANDARD_MODULES)

    Some(filtered)
  }

  override def dependencies = Set(ModuleProperty.Unrolled)

  override def transformations = Set(ModuleProperty.Inlined)
}
