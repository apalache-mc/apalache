package at.forsyte.apalache.io.annotations

import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.json.JsonTlaWriter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.io.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import com.google.inject.{Inject, Singleton}

import java.io.PrintWriter

@Singleton
class PrettyWriterWithAnnotationsFactory @Inject() (sourceStore: SourceStore, changeListener: ChangeListener,
    store: AnnotationStore)
    extends TlaWriterFactory {
  override def createTlaWriter(printWriter: PrintWriter): TlaWriter = {
    new PrettyWriterWithAnnotations(store, printWriter)
  }

  override def createJsonWriter(printWriter: PrintWriter): TlaWriter = {
    new JsonTlaWriter(sourceStore, changeListener, printWriter)
  }
}
