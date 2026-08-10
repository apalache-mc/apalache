package at.forsyte.apalache.io.annotations

import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.OutputWorkspace
import at.forsyte.apalache.io.json.JsonTlaWriter
import at.forsyte.apalache.tla.lir.src.SourceStore
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import com.google.inject.{Inject, Singleton}

import java.io.BufferedWriter

@Singleton
class PrettyWriterWithAnnotationsFactory @Inject() (
    sourceStore: SourceStore,
    changeListener: ChangeListener,
    store: AnnotationStore,
    override protected val outputWorkspace: OutputWorkspace)
    extends TlaWriterFactory {
  override def createTlaWriter(writer: BufferedWriter): TlaWriter = {
    new PrettyWriterWithAnnotations(store, writer)
  }

  override def createJsonWriter(writer: BufferedWriter): TlaWriter = {
    new JsonTlaWriter(sourceStore, changeListener, writer)
  }
}
