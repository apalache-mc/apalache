package at.forsyte.apalache.io.annotations.parser

import java.io.Reader
import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers

/**
 * <p>A lexer for annotations that are hidden in TLA+ comments. Since the annotations are hidden in comments, it is
 * tricky to parse comments like that. Internally, the lexer is producing junk tokens and then filtering them out. </p>
 *
 * @author
 *   Igor Konnov
 */
object AnnotationLexer extends RegexParsers {
  override def skipWhitespace: Boolean = true

  override val whiteSpace: Regex = """([ \t\r\f\n]+)""".r

  /**
   * Parse the input stream and return the list of tokens. Although collecting the list of all tokens in memory is not
   * optimal, streams of tokens produced from comments are supposed to be small.
   *
   * @param reader
   *   a Java reader
   * @return
   *   the list of parsed tokens
   * @throws AnnotationParserError
   *   when the lexer finds an error
   */
  def apply(reader: Reader): Either[String, Seq[AnnotationToken]] = parse(program, reader) match {
    case Success(result, _) =>
      Right(result)

    case NoSuccess(msg, _) =>
      // we ignore the position, as it is the position that is relative to a comment
      Left(msg)
  }

  def program: Parser[Seq[AnnotationToken]] = phrase(rep1(token))

  def token: Parser[AnnotationToken] =
    positioned(
        leftParen | rightParen | comma | dot | boolean | atIdentifier | identifier | number | string | inline_string | unexpected_char
    ) ///

  def skip: Parser[Unit] = rep(whiteSpace) ^^^ ()

  def linefeed: Parser[Unit] = "\n" ^^^ ()

  private def identifier: Parser[IDENT] = {
    "[a-zA-Z_][a-zA-Z0-9_]*".r ^^ { name => IDENT(name) }
  }

  private def atIdentifier: Parser[AT_IDENT] = {
    "@[a-zA-Z_][a-zA-Z0-9_]*".r ^^ { name => AT_IDENT(name.substring(1)) }
  }

  private def string: Parser[STRING] = {
    """"[a-zA-Z0-9_~!@#\\$%^&*\-+=|(){}\[\],:;`'<>.?/ \t\r\f\n]*"""".r ^^ { name =>
      STRING(name.substring(1, name.length - 1))
    }
  }

  private def inline_string: Parser[INLINE_STRING] = {
    """:[a-zA-Z0-9_~!#\\$%^&*\-+=|(){}\[\],:`'<>.?/ \t\r\f\n]*;""".r ^^ { text =>
      val contents = text.substring(1, text.length - 1)
      // Inline string may contain line feeds and other control characters. Remove them.
      val cleared = whiteSpace.replaceAllIn(contents, " ")
      INLINE_STRING(cleared)
    }
  }

  private def unexpected_char: Parser[Nothing] = {
    failure("Unexpected character. Missing ')' or ';'?")
  }

  private def number: Parser[NUMBER] = {
    "(|-)[0-9][0-9]*".r ^^ { value => NUMBER(BigInt(value)) }
  }

  private def boolean: Parser[BOOLEAN] = {
    "(FALSE|TRUE|false|true|False|True)".r ^^ { value => BOOLEAN(value.toBoolean) }
  }

  private def leftParen: Parser[LPAREN] = {
    "(" ^^ (_ => LPAREN())
  }

  private def rightParen: Parser[RPAREN] = {
    ")" ^^ (_ => RPAREN())
  }

  private def comma: Parser[COMMA] = {
    "," ^^ (_ => COMMA())
  }

  private def dot: Parser[DOT] = {
    "." ^^ (_ => DOT())
  }
}
