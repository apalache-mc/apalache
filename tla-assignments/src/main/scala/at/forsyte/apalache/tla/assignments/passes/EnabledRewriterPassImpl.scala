package at.forsyte.apalache.tla.assignments.passes

import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.pp.EnabledRewriter
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker

/**
 * Rewrites ENABLED conditions
 */
class EnabledRewriterPassImpl @Inject() (
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory,
    sourceStore: SourceStore,
    changeListener: ChangeListener)
    extends EnabledRewriterPass with LazyLogging {

  override def name: String = "EnabledRewriterPass"

  override def execute(tlaModule: TlaModule): PassResult = {
    val enabledRewriter = new EnabledRewriter(tracker, sourceStore, changeListener)

    val newModule = new TlaModule(
        tlaModule.name,
        tlaModule.varDeclarations ++
          tlaModule.constDeclarations ++
          tlaModule.assumeDeclarations ++
          tlaModule.operDeclarations.map(operDecl =>
            new TlaOperDecl(
                operDecl.name,
                operDecl.formalParams,
                enabledRewriter(operDecl.body, tlaModule),
            )(operDecl.typeTag)),
    )

    writeOut(writerFactory, newModule)

    Right(newModule)
  }

  override def dependencies = Set(ModuleProperty.Configured, ModuleProperty.Inlined)

  override def transformations = Set(ModuleProperty.EnabledRewritten)
}
