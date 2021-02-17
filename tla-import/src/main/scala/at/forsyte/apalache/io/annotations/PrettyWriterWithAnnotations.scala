package at.forsyte.apalache.io.annotations

import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.lir.TlaDecl
import at.forsyte.apalache.tla.lir.io.{PrettyWriter, TlaWriter}

import java.io.PrintWriter

/**
 * A decorator of PrettyWriter that prints code annotations.
 *
 * @author Igor Konnov
 */
class PrettyWriterWithAnnotations(annotationStore: AnnotationStore, writer: PrintWriter, textWidth: Int = 80,
    indent: Int = 2)
    extends PrettyWriter(writer, textWidth, indent) with TlaWriter {

  // override the translation of a declaration
  override def toDoc(decl: TlaDecl): Doc = {
    val underlyingDoc = super.toDoc(decl)
    annotationStore
      .get(decl.ID)
      .flatMap { annotations =>
        Some(annotations.foldRight(underlyingDoc) { (anno, doc) =>
          // A simple implementation that is using Annotation.toPrettyString.
          // In the future, we should implement a full pretty printer both for annotations and types.
          "(*" <> space <> anno.toPrettyString <> space <> "*)" <>
            linebreak <> doc
        })
      }
      .getOrElse(underlyingDoc)
  }
}
