package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.io.TlaWriterFactory
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.{TlaModule, TlaOperDecl}
import at.forsyte.apalache.tla.pp.{NormalizedNames, OperAppToLetInDef, UniqueNameGenerator}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

import java.io.File
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

    val appWrap = OperAppToLetInDef(gen, tracker)
    val operNames = (baseModule.operDeclarations map {
      _.name
    }).toSet
    val module = appWrap.moduleTransform(operNames)(baseModule)

    val defBodyMap = BodyMapFactory.makeFromDecls(module.operDeclarations)

    val transformationSequence =
      List(
          InlinerOfUserOper(defBodyMap, tracker),
          LetInExpander(tracker, keepNullary = false),
          // the second pass of Inliner may be needed, when the higher-order operators were inlined by LetInExpander
          InlinerOfUserOper(defBodyMap, tracker)
      ) ///

    val inlined = transformationSequence.foldLeft(module) { case (m, tr) =>
      logger.info("  > %s".format(tr.getClass.getSimpleName))
      ModuleByExTransformer(tr)(m)
    }

    // Fixing issue 283: https://github.com/informalsystems/apalache/issues/283
    // Remove the operators that are not needed,
    // as some of them may contain higher-order operators that cannot be substituted
    val relevantOperators = NormalizedNames.userOperatorNamesFromOptions(options).toSet

    // Since PrimingPass now happens before inlining, we have to add InitPrime and CInitPrime as well
    val initName = options.getOrElse("checker", "init", "Init")
    val cinitName = options.getOrElse("checker", "cinit", "CInit")
    val initPrimedName = initName + "Primed"
    val cinitPrimedName = cinitName + "Primed"
    val relevantOperatorsAndInitCInitPrimed = relevantOperators + initPrimedName + cinitPrimedName
    logger.info("Leaving only relevant operators: " + relevantOperatorsAndInitCInitPrimed.toList.sorted.mkString(", "))
    val filteredDefs = inlined.declarations.filter {
      case TlaOperDecl(name, _, _) =>
        relevantOperatorsAndInitCInitPrimed.contains(name)
      case _ => true // accept all other declarations
    }

    val filtered = new TlaModule(inlined.name, filteredDefs)

    // dump the result of preprocessing
    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    writerFactory.writeModuleToFile(filtered, new File(outdir.toFile, "out-inline.tla"))

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
