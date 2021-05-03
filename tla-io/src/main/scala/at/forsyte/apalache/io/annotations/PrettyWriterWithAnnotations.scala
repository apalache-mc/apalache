package at.forsyte.apalache.io.annotations

import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx, TlaModule}
import at.forsyte.apalache.io.lir._

import java.io.PrintWriter

/**
 * A decorator of PrettyWriter that prints code annotations.
 *
 * @author Igor Konnov
 */
class PrettyWriterWithAnnotations(annotationStore: AnnotationStore, writer: PrintWriter,
    layout: TextLayout = TextLayout())
    extends TlaWriter {

  private object annotator extends TlaDeclAnnotator {
    override def apply(layout: TextLayout)(decl: TlaDecl): Option[List[String]] = {
      annotationStore.get(decl.ID) match {
        case None | Some(List()) =>
          None

        case Some(annotations) =>
          Some(annotations.map(_.toPrettyString))
      }
    }
  }

  private val prettyWriter: PrettyWriter = new PrettyWriter(writer, layout, annotator)

  /**
   * Write a module, including all declarations
   *
   * @param mod a module
   */
  override def write(mod: TlaModule, extendedModuleNames: List[String]): Unit = {
    prettyWriter.write(mod, extendedModuleNames)
  }

  /**
   * Write a declaration, including all expressions
   *
   * @param decl a declaration
   */
  override def write(decl: TlaDecl): Unit = {
    prettyWriter.write(decl)
  }

  /**
   * Write a TLA+ expression.
   *
   * @param expr an expression
   */
  override def write(expr: TlaEx): Unit = {
    prettyWriter.write(expr)
  }
}
