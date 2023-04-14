package at.forsyte.apalache.tla.passes.pp

import at.forsyte.apalache.infra.passes.DerivedPredicates
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.transformations.{TlaModuleTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}
import at.forsyte.apalache.tla.pp.{Desugarer, Keramelizer, LetInApplier, Normalizer, UniqueNameGenerator}
import com.google.inject.Inject

/**
 * A preprocessing pass that simplifies TLA+ expression by running multiple transformation.
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
class PreproPassImpl @Inject() (
    options: OptionGroup.HasChecker,
    derivedPreds: DerivedPredicates,
    gen: UniqueNameGenerator,
    renaming: IncrementalRenaming,
    tracker: TransformationTracker,
    sourceStore: SourceStore,
    changeListener: ChangeListener,
    writerFactory: TlaWriterFactory)
    extends PreproPassPartial(
        options,
        derivedPreds,
        renaming,
        tracker,
        sourceStore,
        changeListener,
        writerFactory,
    ) {

  override def execute(tlaModule: TlaModule): PassResult = {
    logger.info("  > Before preprocessing: unique renaming")
    val varSet = tlaModule.varDeclarations.map(_.name).toSet

    val transformationSequence: List[(String, TlaModuleTransformation)] =
      List(
          ("PrimePropagation", createModuleTransformerForPrimePropagation(varSet)),
          ("Desugarer", ModuleByExTransformer(Desugarer(gen, varSet, tracker))),
          ("LetInApplier", ModuleByExTransformer(LetInApplier(tracker))),
          ("UniqueRenamer", renaming.renameInModule),
          ("Normalizer", ModuleByExTransformer(Normalizer(tracker))),
          ("Keramelizer", ModuleByExTransformer(Keramelizer(gen, tracker))),
      )

    executeWithParams(tlaModule, transformationSequence, postRename = true, KeraLanguagePred())
  }

  override def dependencies = Set(ModuleProperty.Inlined)

  override def transformations = Set(ModuleProperty.Preprocessed)

}
