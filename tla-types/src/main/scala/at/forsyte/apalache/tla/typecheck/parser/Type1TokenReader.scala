package at.forsyte.apalache.tla.typecheck.parser

import scala.util.parsing.input.{NoPosition, Position, Reader}

class Type1TokenReader(tokens: Seq[Type1Token]) extends Reader[Type1Token] {
  override def first: Type1Token = tokens.head
  override def atEnd: Boolean = tokens.isEmpty
  override def pos: Position = if (tokens.isEmpty) NoPosition else tokens.head.pos
  override def rest: Reader[Type1Token] = new Type1TokenReader(tokens.tail)
}

