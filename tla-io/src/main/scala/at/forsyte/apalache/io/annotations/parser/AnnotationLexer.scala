package at.forsyte.apalache.io.annotations.parser

import java.io.Reader
import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers
import at.forsyte.apalache.io.annotations.AnnotationParserError

/**
 * <p>A lexer for annotations that are hidden in TLA+ comments. Since the annotations are hidden in comments, it is
 * tricky to parse comments like that. Internally, the lexer is producing junk tokens and then filtering them out. </p>
 *
 * @author
 *   Igor Konnov
 */
object AnnotationLexer extends RegexParsers {
  override def skipWhitespace: Boolean = true

  // We cannot throw away new lines, or else we lose the ability to parse out one line comments in annotations
  // See https://github.com/apalache-mc/apalache/issues/2162
  override val whiteSpace: Regex = """([ \t\f]+)""".r

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

    case Error(msg, _)   => throw new AnnotationParserError(msg)
    case Failure(msg, _) => throw new AnnotationParserError(msg)
  }

  def program: Parser[Seq[AnnotationToken]] = phrase(rep1(token))

  def token: Parser[AnnotationToken] =
    positioned(
        leftParen
          | rightParen
          | comma
          | dot
          | boolean
          | atIdentifier
          | identifier
          | number
          | string
          | inline_string
          | unexpected_char
          | newline
    ) ///

  def skip: Parser[Unit] = rep(whiteSpace) ^^^ ()

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

  // All the valid inline string chars `whiteSpace`
  private val inline_string_chars = """[a-zA-Z0-9_~!#\\$%^&*\-+=|(){}\[\],:`'<>.?/\r\n \t\f]*""".r

  // "inline_strings" are untokenized strings following a ":" and ending with a ";"
  private def inline_string: Parser[INLINE_STRING] = {
    ":" ~> inline_string_chars <~ ";" ^^ { case text =>
      // Inline string may contain control characters that we can safely replace with a space.
      // We also trim leading and trailing whitespace, as it creates noise.
      val cleared = whiteSpace.replaceAllIn(text.trim(), " ")
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

  private def newline: Parser[NL] = {
    """\r?\n""".r ^^^ NL()
  }
}
