package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.transformations.{TlaModuleTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.tla.pp.{Normalizer, UniqueNameGenerator}
import com.google.inject.Inject

/**
 * A preprocessing pass that simplifies TLA+ expressions by running multiple transformations.
 *
 * @param options
 *   pass options
 * @param gen
 *   name generator
 * @param tracker
 *   transformation tracker
 * @param nextPass
 *   next pass to call
 */
class ReTLAPreproPassImpl @Inject() (
    options: PassOptions,
    gen: UniqueNameGenerator,
    renaming: IncrementalRenaming,
    tracker: TransformationTracker,
    sourceStore: SourceStore,
    changeListener: ChangeListener,
    writerFactory: TlaWriterFactory)
    extends PreproPassPartial(
        options,
        renaming,
        tracker,
        sourceStore,
        changeListener,
        writerFactory,
    ) {

  override def execute(tlaModule: TlaModule): Option[TlaModule] = {
    val varSet = tlaModule.varDeclarations.map(_.name).toSet

    val transformationSequence: List[(String, TlaModuleTransformation)] =
      List(
          ("UnchangedUnroll", ModuleByExTransformer(SimpleUnchangedUnroller(tracker))),
          ("PrimePropagation", createModuleTransformerForPrimePropagation(varSet)),
          ("UniqueRenamer", renaming.renameInModule),
          ("Normalizer", ModuleByExTransformer(Normalizer(tracker))),
      )

    // Doesn't need a postRename, since Normalizer won't introduce bound vars
    executeWithParams(tlaModule, transformationSequence, postRename = false, ReTLALanguagePred())
  }

  override def dependencies = Set(ModuleProperty.Inlined)

  override def transformations = Set(ModuleProperty.Preprocessed)

}
