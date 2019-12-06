package at.forsyte.apalache.io.tlc

import at.forsyte.apalache.io.tlc.config._

import scala.util.parsing.combinator.RegexParsers

/**
  * A lexer for the TLC configuration files.
  *
  * @author Igor Konnov
  */
object TlcConfigLexer extends RegexParsers {
  override def skipWhitespace: Boolean = true

  def identifier: Parser[Ident] = {
    "[a-zA-Z_][a-zA-Z0-9_]*".r ^^ { name => Ident(name) }
  }

  def constant: Parser[Constant] = {
    "CONSTANT(S|)".r  ^^ (_ => Constant())
  }

  def init: Parser[Init] = {
    "INIT"  ^^ (_ => Init())
  }

  def next: Parser[Next] = {
    "NEXT"  ^^ (_ => Next())
  }

  def specification: Parser[Specification] = {
    "SPECIFICATION" ^^ (_ => Specification())
  }

  def invariant: Parser[Invariant] = {
    "INVARIANT" ^^ (_ => Invariant())
  }

  def property: Parser[Property] = {
    "PROPERT(Y|IES)" ^^ (_ => Property())
  }

  def constraint: Parser[Constraint] = {
    "CONSTRAINT" ^^ (_ => Constraint())
  }

  def assign: Parser[Assign] = {
    "<-" ^^ (_ => Assign())
  }

  def eq: Parser[Eq] = {
    "=" ^^ (_ => Eq())
  }
}
