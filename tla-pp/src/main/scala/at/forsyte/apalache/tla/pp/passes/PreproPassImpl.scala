package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.transformations.{
  PredResultFail, PredResultOk, TlaModuleTransformation, TransformationTracker,
}
import at.forsyte.apalache.tla.lir.{TlaDecl, TlaModule, TlaOperDecl, UID, ModuleProperty}
import at.forsyte.apalache.tla.pp.{Desugarer, Keramelizer, Normalizer, UniqueNameGenerator}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * A preprocessing pass that simplifies TLA+ expression by running multiple transformation.
 *
 * @param options pass options
 * @param gen     name generator
 * @param tracker  transformation tracker
 * @param nextPass next pass to call
 */
class PreproPassImpl @Inject() (
    options: PassOptions, gen: UniqueNameGenerator, renaming: IncrementalRenaming, tracker: TransformationTracker,
    sourceStore: SourceStore, changeListener: ChangeListener, writerFactory: TlaWriterFactory,
    @Named("AfterPrepro") val nextPass: Pass with TlaModuleMixin,
) extends PreproPassPartial(
        options,
        renaming,
        tracker,
        sourceStore,
        changeListener,
        writerFactory,
        nextPass,
    ) {

  /**
   * Run the pass.
   *
   * @return true, if the pass was successful
   */
  override def execute(): Boolean = {
    logger.info("  > Before preprocessing: unique renaming")
    val input = tlaModule.get
    val varSet = input.varDeclarations.map(_.name).toSet

    val transformationSequence: List[(String, TlaModuleTransformation)] =
      List(
          ("PrimePropagation", createModuleTransformerForPrimePropagation(varSet)),
          ("Desugarer", ModuleByExTransformer(Desugarer(gen, tracker))),
          ("UniqueRenamer", renaming.renameInModule),
          ("Normalizer", ModuleByExTransformer(Normalizer(tracker))),
          ("Keramelizer", ModuleByExTransformer(Keramelizer(gen, tracker))),
      )

    executeWithParams(transformationSequence, postRename = true, KeraLanguagePred())
  }

  override def dependencies = Set(ModuleProperty.Inlined)

  override def transformations = Set(ModuleProperty.Preprocessed)

}
