package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.ModuleProperty
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.lir.transformations._
import at.forsyte.apalache.tla.pp._
import com.google.inject.Inject

/**
 * A pass that expands operators and let-in definitions.
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
class ReTLAInlinePassImpl @Inject() (
    options: PassOptions,
    gen: UniqueNameGenerator,
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory)
    extends PartialInlinePassImpl(options, tracker, writerFactory) {

  override val transformationSequence: List[BodyMap => TlaExTransformation] = {
    List(
        InlinerOfUserOper(_, tracker),
        _ => LetInExpander(tracker, keepNullary = false), // expand all LET-IN
        // No HO operators in reTLA, so we don't need a 2nd inliner run
    )
  }

  override def dependencies = Set()
  override def transformations = Set(ModuleProperty.Inlined, ModuleProperty.Unrolled)
}
