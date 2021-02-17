package at.forsyte.apalache.io.annotations

import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.lir.io.{TlaWriter, TlaWriterFactory}
import com.google.inject.{Inject, Singleton}

import java.io.PrintWriter

@Singleton
class PrettyWriterWithAnnotationsFactory @Inject() (store: AnnotationStore) extends TlaWriterFactory {
  override def create(printWriter: PrintWriter): TlaWriter = {
    new PrettyWriterWithAnnotations(store, printWriter)
  }
}
