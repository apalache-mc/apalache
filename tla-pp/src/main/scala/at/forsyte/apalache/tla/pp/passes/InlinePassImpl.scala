package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.lir.storage.{BodyMap, BodyMapFactory}
import at.forsyte.apalache.tla.lir.transformations._
import at.forsyte.apalache.tla.lir.transformations.standard.{ModuleByExTransformer, IncrementalRenaming}
import at.forsyte.apalache.tla.lir.{TlaModule, TlaOperDecl}
import at.forsyte.apalache.tla.pp._
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

import java.nio.file.Path

/**
 * A pass that expands operators and let-in definitions.
 *
 * @param options  pass options
 * @param gen      name generator
 * @param tracker  transformation tracker
 * @param nextPass next pass to call
 */
class InlinePassImpl @Inject() (val options: PassOptions, gen: UniqueNameGenerator, renaming: IncrementalRenaming,
    tracker: TransformationTracker, writerFactory: TlaWriterFactory,
    @Named("AfterInline") nextPass: Pass with TlaModuleMixin)
    extends InlinePass with LazyLogging {

  private var outputTlaModule: Option[TlaModule] = None

  /**
   * The pass name.
   *
   * @return the name associated with the pass
   */
  override def name: String = "InlinePass"

  /**
   * Run the pass.
   *
   * @return true, if the pass was successful
   */
  override def execute(): Boolean = {
    val baseModule = tlaModule.get

    /*
    Disable the preprocessing pass that introduces nullary operators for call results.
    We have to integrate it properly with the type checker.

    val appWrap = OperAppToLetInDef(gen, tracker)
    val operNames = (baseModule.operDeclarations map {
      _.name
    }).toSet
    val module = appWrap.moduleTransform(operNames)(baseModule)
     */
    val module = baseModule

    val transformationSequence: List[BodyMap => TlaExTransformation] = {
      val wrapHandler = CallByNameWrapHandler(tracker)
      List(
          InlinerOfUserOper(_, tracker),
          _ => wrapHandler.wrap, // wrap to identify call-by name
          CallByNameOperatorEmbedder(tracker, _, gen), // create local definitions at call sites
          _ => LetInExpander(tracker, keepNullary = true), // expand LET-IN, but ignore call-by-name
          _ => wrapHandler.unwrap, // unwrap, to remove ApalacheOper.callByName
          // the second pass of Inliner may be needed, when the higher-order operators were inlined by LetInExpander
          InlinerOfUserOper(_, tracker)
      )
    }

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
    val constants = module.constDeclarations map { _.name }
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
        declarations = inlined.declarations map declTr
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

    outputTlaModule = Some(filtered)
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
      nextPass.setModule(m)
      nextPass
    }
  }
}
