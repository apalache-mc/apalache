package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.AnnotationParser
import at.forsyte.apalache.io.annotations.AnnotationParser.{Failure, Success}
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.lir.UID
import com.typesafe.scalalogging.LazyLogging
import tla2sany.semantic.{OpDefNode, OpDefOrDeclNode}

/**
 * This class extracts annotations from the strings that are attached to a SemanticNode.
 *
 * @author Igor Konnov
 */
class AnnotationExtractor(annotationStore: AnnotationStore) extends LazyLogging {
  def parseAndSave(uid: UID, node: OpDefOrDeclNode): Unit = {
    val commentText = locateComments(node)
    AnnotationParser.parse(commentText) match {
      case Success(annotations) =>
        annotationStore += uid -> annotations

      case Failure(message) =>
        // Warn the user and continue. It may be a piece of text that looks like an annotation, but it is not an annotation.
        logger.warn("%s: Failed to parse annotations in the comments. This may lead to a type error later.",
            node.getLocation.toString)
        logger.warn(message)
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
