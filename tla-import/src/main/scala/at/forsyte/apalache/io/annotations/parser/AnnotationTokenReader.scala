package at.forsyte.apalache.io.annotations.parser

import scala.util.parsing.input.{NoPosition, Position, Reader}

class AnnotationTokenReader(tokens: Seq[AnnotationToken]) extends Reader[AnnotationToken] {
  override def first: AnnotationToken = tokens.head

  override def atEnd: Boolean = tokens.isEmpty

  override def pos: Position = if (tokens.isEmpty) NoPosition else tokens.head.pos

  override def rest: Reader[AnnotationToken] = new AnnotationTokenReader(tokens.tail)
}
