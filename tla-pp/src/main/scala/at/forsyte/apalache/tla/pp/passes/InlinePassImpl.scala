package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.io.lir.TlaWriterFactory
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
class InlinePassImpl @Inject() (
    options: PassOptions,
    gen: UniqueNameGenerator,
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory)
    extends PartialInlinePassImpl(options, tracker, writerFactory) {

  override val transformationSequence: List[BodyMap => TlaExTransformation] = {
    val wrapHandler = CallByNameWrapHandler(tracker)
    List(
        InlinerOfUserOper(_, tracker),
        _ => wrapHandler.wrap, // wrap to identify call-by name
        CallByNameOperatorEmbedder(tracker, _, gen), // create local definitions at call sites
        _ => LetInExpander(tracker, keepNullary = true), // expand LET-IN, but ignore call-by-name
        _ => wrapHandler.unwrap, // unwrap, to remove ApalacheOper.callByName
        // the second pass of Inliner may be needed, when the higher-order operators were inlined by LetInExpander
        InlinerOfUserOper(_, tracker),
    )
  }
}
