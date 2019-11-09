package at.forsyte.apalache.tla.pp.passes

import java.io.File
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.pp.{Desugarer, Keramelizer, Normalizer, UniqueNameGenerator}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * A pass that expands operators and let-in definitions.
  *
  * @param options pass options
  * @param gen name generator
  * @param tracker transformation tracker
  * @param nextPass next pass to call
  */
class InlinePassImpl @Inject()(val options: PassOptions,
                               gen: UniqueNameGenerator,
                               renaming: IncrementalRenaming,
                               tracker: TransformationTracker,
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
    val module = tlaModule.get
    val defBodyMap = BodyMapFactory.makeFromDecls(module.operDeclarations)

    val transformationSequence =
      List(
        InlinerOfUserOper(defBodyMap, tracker),
        LetInExpander(tracker, keepNullary = true)
      )

    val inlined = transformationSequence.foldLeft(module){
      case (m, tr) =>
        logger.info("  > %s".format(tr.getClass.getSimpleName))
        ModuleByExTransformer(tr) (m)
    }

    // dump the result of preprocessing
    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    PrettyWriter.write(inlined, new File(outdir.toFile, "out-inline.tla"))

    outputTlaModule = Some(inlined)
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
      nextPass.setModule( m )
      nextPass
    }
  }
}
