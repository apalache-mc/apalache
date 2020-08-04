package at.forsyte.apalache.tla.typecheck.parser

import java.io.Reader

import at.forsyte.apalache.io.tlc.config.TlcConfigParseError

import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers

object Type1Lexer extends RegexParsers {
  override def skipWhitespace: Boolean = true

  override val whiteSpace: Regex = "[ \t\r\f]+".r   // no linefeeds

  /**
    * Parse the input stream and return the list of tokens. Although collecting the list of all tokens in memory is
    * not optimal, TLC configurations files are tiny, so it should not be a big deal.
    *
    * @param reader a Java reader
    * @return the list of parsed tokens
    * @throws TlcConfigParseError when the lexer finds an error
    */
  def apply(reader: Reader): List[Type1Token] = parseAll(expr, reader) match {
    case Success(result, _) => result
    case NoSuccess(msg, next) => throw new Type1ParseError(msg, next.pos)
  }

  def expr: Parser[List[Type1Token]] = skip ~> rep(token <~ skip) <~ eof

  def eof: Parser[String] = "\\z".r | failure("unexpected character")

  def token: Parser[Type1Token] =
    positioned(
      int | bool | str | set | seq |
        capsIdentifier | letterIdentifier | rightArrow | doubleRightArrow | leftParen | rightParen
    ) ///

  // it is important that linefeed is not a whiteSpace, as otherwise singleComment consumes the whole input!
  def skip: Parser[Unit] = rep(whiteSpace) ^^^ Unit

  private def capsIdentifier: Parser[CAPS_IDENT] = {
    "[A-Z_][A-Z0-9_]*".r ^^ { name => CAPS_IDENT(name) }
  }

  private def letterIdentifier: Parser[LETTER_IDENT] = {
    "[a-z]".r ^^ { name => LETTER_IDENT(name) }
  }

  private def int: Parser[INT] = {
    "Int".r ^^ { _ => INT() }
  }

  private def bool: Parser[BOOL] = {
    "Bool".r ^^ { _ => BOOL() }
  }

  private def str: Parser[STR] = {
    "Str".r ^^ { _ => STR() }
  }

  private def set: Parser[SET] = {
    "Set".r ^^ { _ => SET() }
  }

  private def seq: Parser[SEQ] = {
    "Seq".r ^^ { _ => SEQ() }
  }

  private def rightArrow: Parser[RIGHT_ARROW] = {
    "->".r ^^ { _ => RIGHT_ARROW() }
  }

  private def doubleRightArrow: Parser[DOUBLE_RIGHT_ARROW] = {
    "=>".r ^^ { _ => DOUBLE_RIGHT_ARROW() }
  }

  private def leftParen: Parser[LPAREN] = {
    "(" ^^ { _ => LPAREN() }
  }

  private def rightParen: Parser[RPAREN] = {
    ")" ^^ { _ => RPAREN() }
  }

  private def doubleLeftAngle: Parser[DOUBLE_LEFT_ANGLE] = {
    "<<".r ^^ { _ => DOUBLE_LEFT_ANGLE() }
  }

  private def doubleRightAngle: Parser[DOUBLE_RIGHT_ANGLE] = {
    ">>".r ^^ { _ => DOUBLE_RIGHT_ANGLE() }
  }
}

