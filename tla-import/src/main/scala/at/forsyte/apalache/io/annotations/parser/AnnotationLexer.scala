package at.forsyte.apalache.io.annotations.parser

import at.forsyte.apalache.io.annotations.AnnotationParserError

import java.io.Reader
import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers

/**
 * <p>A lexer for annotations that are hidden in TLA+ comments.
 * Since the annotations are hidden in comments, it is tricky to parse comments like that.
 * Internally, the lexer is producing junk tokens and then filtering them out.
 * </p>
 *
 * @author Igor Konnov
 */
object AnnotationLexer extends RegexParsers {
  override def skipWhitespace: Boolean = true

  override val whiteSpace: Regex = """([ \t\r\f\n]+|\\\*|\(\*|\*\))""".r

  /**
   * Parse the input stream and return the list of tokens. Although collecting the list of all tokens in memory is
   * not optimal, streams of tokens produced from comments are supposed to be small.
   *
   * @param reader a Java reader
   * @return the list of parsed tokens
   * @throws AnnotationParserError when the lexer finds an error
   */
  def apply(reader: Reader): Seq[AnnotationToken] = parseAll(program, reader) match {
    case Success(result, _) =>
      result

    case NoSuccess(msg, _) =>
      // we ignore the position, as it is the position that is relative to a comment
      throw new AnnotationParserError(msg)
  }

  def program: Parser[Seq[AnnotationToken]] = {
    skip ~> rep(token <~ skip) <~ eof ^^ { tokens => tokens.filter(_ != JUNK()) }
  }

  def eof: Parser[String] = "\\z".r | failure("unexpected character")

  def token: Parser[AnnotationToken] =
    positioned(
        leftParen | rightParen | comma | dot | boolean | atIdentifier | identifier | number | string | inline_string | junk
    ) ///

  def skip: Parser[Unit] = rep(whiteSpace) ^^^ Unit

  def linefeed: Parser[Unit] = "\n" ^^^ Unit

  private def identifier: Parser[IDENT] = {
    "[a-zA-Z_][a-zA-Z0-9_]*".r ^^ { name => IDENT(name) }
  }

  private def atIdentifier: Parser[AT_IDENT] = {
    "@[a-zA-Z_][a-zA-Z0-9_]*".r ^^ { name => AT_IDENT(name.substring(1)) }
  }

  private def string: Parser[STRING] = {
    """"[a-zA-Z0-9_~!@#\\$%^&*\-+=|(){}\[\],:;`'<>.?/ \t\r\f\n]*"""".r ^^ { name =>
      STRING(removeLeadingCommentsAndControlChars(name.substring(1, name.length - 1)))
    }
  }

  private def inline_string: Parser[INLINE_STRING] = {
    """:[a-zA-Z0-9_~!@#\\$%^&*\-+=|(){}\[\],:`'<>.?/ \t\r\f\n]*;""".r ^^ { name =>
      INLINE_STRING(removeLeadingCommentsAndControlChars(name.substring(1, name.length - 1)))
    }
  }

  /**
   * <p>It is not uncommon to write multiline strings in annotations. Since these strings are written in comments,
   * it should be possible to write them like:</p>
   *
   * <pre>
   *
   * \* @type: Int
   * \*          => Int;
   * \*
   * \* @type("Int
   * \*          => Int")
   * </pre>
   *
   * <p>This method removes the leading "\*" from a multiline string. Additionally, it replaces with a space
   * a group of carriage returns, form feeds, line feeds, and tabs.</p>
   *
   * @param text text to preprocess
   * @return text without leading "\*" and ASCII control characters
   */
  private def removeLeadingCommentsAndControlChars(text: String): String = {
    text.replaceAll("""\n[ \t\r\f]*\\\*""", "").replaceAll("[\n\t\r\f]*", "")
  }

  private def number: Parser[NUMBER] = {
    "(|-)[0-9][0-9]*".r ^^ { value => NUMBER(value.toInt) }
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

  // Whatever is not recognized as a token above, should be treated as junk.
  // We take care of not consuming the character '@' as junk, if it is followed by a letter or underscore.
  private def junk: Parser[JUNK] = {
    "(@[^a-zA-Z_]|[^@]+)".r ^^ { _ => JUNK() }
  }
}
