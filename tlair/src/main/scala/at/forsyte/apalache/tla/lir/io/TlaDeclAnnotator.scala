package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir.TlaDecl

/**
 * An interface for additional decorators of declarations that can be used in PrettyWriter.
 * The default behavior is to do nothing.
 *
 * @author Igor Konnov
 */
class TlaDeclAnnotator {

  /**
   * Given the text layout settings and a declaration, produce a string representation of an annotation,
   * which respects the layout settings.
   *
   * @param layout layout settings
   * @param decl   declaration to annotate
   * @return a string annotation
   */
  def apply(layout: TextLayout)(decl: TlaDecl): Option[List[String]] = None
}
