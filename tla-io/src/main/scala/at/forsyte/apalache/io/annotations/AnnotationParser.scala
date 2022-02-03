package at.forsyte.apalache.io.annotations

import at.forsyte.apalache.io.annotations.parser._

import java.io.{Reader, StringReader}
import scala.util.parsing.combinator.Parsers

/**
 * A parser for TLA+ annotations. Use the object TlaAnnotationParser to parse the input.
 *
 * @author Igor Konnov
 */
class AnnotationParser extends Parsers {
  override type Elem = AnnotationToken

  def apply(tokens: Seq[AnnotationToken]): Either[String, Annotation] = {
    val reader = new AnnotationTokenReader(tokens)
    annotation(reader) match {
      case Success(annotation: Annotation, _) =>
        Right(annotation)

      case Failure(msg, _) => Left(msg)

      case Error(msg, _) => Left(msg)
    }
  }

  def annotation: Parser[Annotation] = phrase(atIdent ~ opt(argsInParentheses | argAfterColon)) ^^ {
    case name ~ None =>
      Annotation(name)

    case name ~ Some(args) =>
      Annotation(name, args: _*)
  }

  def argsInParentheses: Parser[List[AnnotationArg]] = LPAREN() ~ repsep(arg, COMMA()) ~ RPAREN() ^^ {
    case _ ~ args ~ _ =>
      args
  }

  def argAfterColon: Parser[List[AnnotationArg]] = inlineString ^^ { str =>
    List(AnnotationStr(str))
  }

  def arg: Parser[AnnotationArg] = stringArg | intArg | boolArg | identArg

  def stringArg: Parser[AnnotationStr] = string ^^ { str =>
    AnnotationStr(str)
  }

  def inlineStringArg: Parser[AnnotationStr] = inlineString ^^ { str =>
    AnnotationStr(str)
  }

  def identArg: Parser[AnnotationIdent] = ident ^^ { name =>
    AnnotationIdent(name)
  }

  def intArg: Parser[AnnotationInt] = number ^^ { num =>
    AnnotationInt(num)
  }

  def boolArg: Parser[AnnotationBool] = boolean ^^ { b =>
    AnnotationBool(b)
  }

  private def ident: Parser[String] = {
    accept("identifier", { case IDENT(name) => name })
  }

  private def atIdent: Parser[String] = {
    accept("@identifier", { case AT_IDENT(name) => name })
  }

  private def number: Parser[BigInt] = {
    accept("number", { case NUMBER(i) => i })
  }

  private def string: Parser[String] = {
    accept("string", { case STRING(s) => s })
  }

  private def inlineString: Parser[String] = {
    accept("inlineString", { case INLINE_STRING(s) => s })
  }

  private def boolean: Parser[Boolean] = {
    accept("boolean", { case BOOLEAN(b) => b })
  }
}

object AnnotationParser {
  private val parser: AnnotationParser = new AnnotationParser

  def parse(reader: Reader): Either[String, Annotation] = {
    for {
      tokens <- AnnotationLexer(reader).right
      ast <- new AnnotationParser()(tokens).right
    } yield ast
  }

  def parse(text: String): Either[String, Annotation] = {
    parse(new StringReader(text))
  }
}
