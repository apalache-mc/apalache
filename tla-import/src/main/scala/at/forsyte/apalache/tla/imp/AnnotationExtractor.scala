package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.AnnotationParser.{Failure, Success}
import at.forsyte.apalache.io.annotations.{Annotation, AnnotationParser}
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.src.SourceLocation
import at.forsyte.apalache.tla.lir.UID
import tla2sany.semantic.OpDefOrDeclNode

/**
  * This class extracts annotations from the strings that are attached to a SemanticNode.
  *
  * @author Igor Konnov
  */
class AnnotationExtractor(annotationStore: AnnotationStore) {
  def parseAndSave(uid: UID, node: OpDefOrDeclNode): Unit = {
    var annotations = List[Annotation]()
    var comments = node.getComment
    var index = 0
    while (index != -1) {
      index = comments.indexOf('@', index)
      if (index != -1) {
        // we have found the starting position of an annotation
        comments = comments.substring(index)
        AnnotationParser.parse(comments) match {
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
}
