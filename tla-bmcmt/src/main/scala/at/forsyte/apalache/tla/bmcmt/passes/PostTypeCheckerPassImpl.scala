package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.typecheck.passes.EtcTypeCheckerPassImpl
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * A copy of EtcTypeCheckerPassImpl that we run after all preprocessing steps.
 * We introduce one more class, as otherwise Google Guice would not let us to use the same pass in the different
 * parts of the pipeline.
 *
 * @param options         options
 * @param sourceStore     source store
 * @param tracker         transformation tracker
 * @param annotationStore annotations store
 * @param nextPass        next pass to be used
 */
class PostTypeCheckerPassImpl @Inject() (options: PassOptions, sourceStore: SourceStore, tracker: TransformationTracker,
    annotationStore: AnnotationStore, @Named("AfterPostTypeChecker") nextPass: Pass with TlaModuleMixin)
    extends EtcTypeCheckerPassImpl(options, sourceStore, tracker, annotationStore, nextPass) with LazyLogging {

  override def name: String = "PostTypeCheckerSnowcat"
}
