package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.AnnotationParser.{Failure, Success}
import at.forsyte.apalache.io.annotations.{Annotation, AnnotationParser}
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.src.SourceLocation
import at.forsyte.apalache.tla.lir.UID
import tla2sany.semantic.{OpDefNode, OpDefOrDeclNode}

/**
 * This class extracts annotations from the strings that are attached to a SemanticNode.
 *
 * @author Igor Konnov
 */
class AnnotationExtractor(annotationStore: AnnotationStore) {
  def parseAndSave(uid: UID, node: OpDefOrDeclNode): Unit = {
    var annotations = List[Annotation]()
    var commentText = locateComments(node)
    var index = 0
    while (index != -1) {
      index = commentText.indexOf('@', index)
      if (index != -1) {
        // we have found the starting position of an annotation
        commentText = commentText.substring(index)
        AnnotationParser.parse(commentText) match {
          case Success(annotation, length) =>
            annotations +:= annotation
            assert(length > 0)
            index = length

          case Failure(message) =>
            val loc = SourceLocation(node.getLocation)
            throw new SanyImporterException(
                "%s: Annotation error: %s".format(loc, message)
            )
        }
      }
    }

    if (annotations.nonEmpty) {
      annotationStore += uid -> annotations.reverse
    }
  }

  private def locateComments: OpDefOrDeclNode => String = {
    case opdef: OpDefNode =>
      // This operator definition can be a copy of a definition that is declared in another module
      // and instantiated with INSTANCE. In this case, getComment would return an empty string when called on `opdef`.
      // That is why we extract the comment from the source node, which is either `opdef`,
      // or the node that was defined in another module.
      opdef.getSource.getComment

    case node =>
      // in this case, we just get the comment above the declaration, e.g., of a VARIABLE or a CONSTANT.
      node.getComment
  }
}
