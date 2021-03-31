package at.forsyte.apalache.tla.typecheck.parser

import java.io.Reader

import at.forsyte.apalache.io.tlc.config.TlcConfigParseError

import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers

private[parser] object Type1Lexer extends RegexParsers {
  override def skipWhitespace: Boolean = true

  override val whiteSpace: Regex = "[ \t\r\f]+".r // no linefeeds

  /**
   * Parse the input stream and return the list of tokens. Although collecting the list of all tokens in memory is
   * not optimal, TLC configurations files are tiny, so it should not be a big deal.
   *
   * @param reader a Java reader
   * @return the list of parsed tokens
   * @throws TlcConfigParseError when the lexer finds an error
   */
  def apply(reader: Reader): List[Type1Token] = parseAll(expr, reader) match {
    case Success(result, _)   => result
    case NoSuccess(msg, next) => throw new Type1ParseError(msg, next.pos)
  }

  def expr: Parser[List[Type1Token]] = skip ~> rep(token <~ skip) <~ eof

  def eof: Parser[String] = "\\z".r | failure("unexpected character")

  def token: Parser[Type1Token] =
    positioned(
        int | real | bool | str | set | seq | identifier | fieldNumber |
          rightArrow | doubleRightArrow | eq | leftParen | rightParen | leftBracket | rightBracket |
          leftCurly | rightCurly | doubleLeftAngle | doubleRightAngle | comma | colon
    ) ///

  // a linefeed is not a white-space
  def skip: Parser[Unit] = rep(whiteSpace) ^^^ Unit

  private def identifier: Parser[IDENT] = {
    "[A-Za-z_][A-Za-z0-9_]*".r ^^ { name => IDENT(name) }
  }

  private def fieldNumber: Parser[FIELD_NO] = {
    "[0-9]+".r ^^ { str => FIELD_NO(Integer.parseInt(str)) }
  }

  private def int: Parser[INT] = {
    "Int".r ^^ { _ => INT() }
  }

  private def real: Parser[REAL] = {
    "Real".r ^^ { _ => REAL() }
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

  private def eq: Parser[EQ] = {
    "=".r ^^ { _ => EQ() }
  }

  private def leftParen: Parser[LPAREN] = {
    "(" ^^ { _ => LPAREN() }
  }

  private def rightParen: Parser[RPAREN] = {
    ")" ^^ { _ => RPAREN() }
  }

  private def leftBracket: Parser[LBRACKET] = {
    "[" ^^ { _ => LBRACKET() }
  }

  private def rightBracket: Parser[RBRACKET] = {
    "]" ^^ { _ => RBRACKET() }
  }

  private def leftCurly: Parser[LCURLY] = {
    "{" ^^ { _ => LCURLY() }
  }

  private def rightCurly: Parser[RCURLY] = {
    "}" ^^ { _ => RCURLY() }
  }

  private def doubleLeftAngle: Parser[DOUBLE_LEFT_ANGLE] = {
    "<<".r ^^ { _ => DOUBLE_LEFT_ANGLE() }
  }

  private def doubleRightAngle: Parser[DOUBLE_RIGHT_ANGLE] = {
    ">>".r ^^ { _ => DOUBLE_RIGHT_ANGLE() }
  }

  private def comma: Parser[COMMA] = {
    ",".r ^^ { _ => COMMA() }
  }

  private def colon: Parser[COLON] = {
    ":".r ^^ { _ => COLON() }
  }
}
