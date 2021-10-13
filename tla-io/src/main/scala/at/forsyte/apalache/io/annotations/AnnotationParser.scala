package at.forsyte.apalache.io.annotations

import at.forsyte.apalache.io.annotations.parser.{
  AT_IDENT, AnnotationLexer, AnnotationToken, AnnotationTokenReader, BOOLEAN, COMMA, DOT, IDENT, INLINE_STRING, LPAREN,
  NUMBER, RPAREN, STRING
}

import java.io.{Reader, StringReader}
import scala.util.parsing.combinator.Parsers

/**
 * A parser for TLA+ annotations. Use the object TlaAnnotationParser to parser the input.
 *
 * @author Igor Konnov
 */
class AnnotationParser extends Parsers {
  override type Elem = AnnotationToken

  def annotationsInText: Parser[List[Annotation]] = rep(junk) ~ repsep(isolatedAnnotation, rep(junk)) ^^ {
    case _ ~ annotations =>
      annotations
  }

  def isolatedAnnotation: Parser[Annotation] = atIdent ~ opt(argsInParentheses | argAfterColon) ^^ {
    case name ~ None =>
      Annotation(name)

    case name ~ Some(args) =>
      Annotation(name, args: _*)
  }

  // As annotations are embedded in text comments, the lexer may recognize some character sequences as tokens.
  // It's OK, we will ignore them.
  private def junk: Parser[String] =
    (ident | string | inlineString | number | boolean | COMMA() | DOT() | LPAREN() | RPAREN()) ^^ { _ =>
      ""
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
  abstract class Result

  case class Success(annotation: List[Annotation]) extends Result

  case class Failure(message: String) extends Result

  private val parser: AnnotationParser = new AnnotationParser

  def parse(reader: Reader): Result = {
    val tokenReader = new AnnotationTokenReader(AnnotationLexer(reader))
    parser.annotationsInText(tokenReader) match {
      case parser.Success(annotations: List[Annotation], _) =>
        Success(annotations)

      case parser.Success(res, _) =>
        Failure("Expected a list of annotations, found: " + res)

      case parser.Failure(msg, _) => Failure(msg)

      case parser.Error(msg, _) => Failure(msg)
    }
  }

  def parse(text: String): Result = {
    parse(new StringReader(text))
  }
}
