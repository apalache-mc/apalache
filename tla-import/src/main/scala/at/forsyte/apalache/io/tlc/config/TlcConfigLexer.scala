package at.forsyte.apalache.io.tlc.config

import java.io.Reader

import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers

/**
  * <p>A lexer for the TLC configuration files.</p>
  *
  * <p>This code follows the
  * <a href="http://nielssp.dk/2015/07/creating-a-scanner-using-parser-combinators-in-scala">tutorial on scanners</a>.</p>
  *
  * @author Igor Konnov
 */
object TlcConfigLexer extends RegexParsers {
  override def skipWhitespace: Boolean = true
  override val whiteSpace: Regex = "[ \t\r\f]+".r // process linefeed separately, in order to parse one-line comments

  /**
    * Parse the input stream and return the list of tokens. Although collecting the list of all tokens in memory is
    * not optimal, TLC configurations files are tiny, so it should not be a big deal.
    *
    * @param reader a Java reader
    * @return the list of parsed tokens
    * @throws TlcConfigParseError when the lexer finds an error
    */
  def apply(reader: Reader): List[TlcConfigToken] = parseAll(program, reader) match {
    case Success(result, _) => result
    case NoSuccess(msg, next) => throw new TlcConfigParseError(msg, next.pos)
  }

  def program: Parser[List[TlcConfigToken]] = skip ~> rep(token <~ skip) <~ eof

  def eof: Parser[String] = "\\z".r | failure("unexpected character")

  def token: Parser[TlcConfigToken] =
    positioned(
      constant | init | next | specification | invariant | property | constraint | actionConstraint |
        symmetry | leftArrow | eq | identifier | number
    ) ///

  // it is important that linefeed is not a whiteSpace, as otherwise singleComment consumes the whole input!
  def skip: Parser[Unit] = rep(whiteSpace | singleComment | multiComment | linefeed) ^^^ Unit

  def linefeed: Parser[Unit] = "\n" ^^^ Unit

  def singleComment: Parser[Unit] = "\\*" ~ rep(not("\n") ~ ".".r) ^^^ Unit

  def multiComment: Parser[Unit] = "(*" ~ rep(not("*)") ~ "(?s).".r) ~ "*)" ^^^ Unit

  private def identifier: Parser[IDENT] = {
    "[a-zA-Z_][a-zA-Z0-9_]*".r ^^ { name => IDENT(name) }
  }

  private def number: Parser[NUMBER] = {
    "(|-)[0-9][0-9]*".r ^^ { value => NUMBER(value) }
  }

  private def constant: Parser[CONST] = {
    "CONSTANT(S|)".r  ^^ (_ => CONST())
  }

  private def init: Parser[INIT] = {
    "INIT"  ^^ (_ => INIT())
  }

  private def next: Parser[NEXT] = {
    "NEXT"  ^^ (_ => NEXT())
  }

  private def specification: Parser[SPECIFICATION] = {
    "SPECIFICATION" ^^ (_ => SPECIFICATION())
  }

  private def invariant: Parser[INVARIANT] = {
    "INVARIANT(S|)".r ^^ (_ => INVARIANT())
  }

  private def property: Parser[PROPERTY] = {
    "PROPERT(Y|IES)".r ^^ (_ => PROPERTY())
  }

  private def constraint: Parser[CONSTRAINT] = {
    "CONSTRAINT(S|)".r ^^ (_ => CONSTRAINT())
  }

  private def actionConstraint: Parser[ACTION_CONSTRAINT] = {
    "ACTION_CONSTRAINT(S|)".r ^^ (_ => ACTION_CONSTRAINT())
  }

  private def symmetry: Parser[SYMMETRY] = {
    "SYMMETRY".r ^^ (_ => SYMMETRY())
  }

  private def leftArrow: Parser[LEFT_ARROW] = {
    "<-" ^^ (_ => LEFT_ARROW())
  }

  private def eq: Parser[EQ] = {
    "=" ^^ (_ => EQ())
  }
}
