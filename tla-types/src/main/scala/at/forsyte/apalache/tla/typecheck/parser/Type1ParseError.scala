package at.forsyte.apalache.tla.typecheck.parser

import scala.util.parsing.input.Position

class Type1ParseError(val msg: String, val pos: Position) extends Exception(msg) {
  override def toString: String = {
    // our parser works over a single string, so only the column is relevant
    "Type parse error at col %s: %s".format(pos.column, msg)
  }
}
