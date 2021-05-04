package at.forsyte.apalache.io.tlc.config

import scala.util.parsing.input.{NoPosition, Position, Reader}

class TlcConfigTokenReader(tokens: Seq[TlcConfigToken]) extends Reader[TlcConfigToken] {
  override def first: TlcConfigToken = tokens.head
  override def atEnd: Boolean = tokens.isEmpty
  override def pos: Position = if (tokens.isEmpty) NoPosition else tokens.head.pos
  override def rest: Reader[TlcConfigToken] = new TlcConfigTokenReader(tokens.tail)
}
