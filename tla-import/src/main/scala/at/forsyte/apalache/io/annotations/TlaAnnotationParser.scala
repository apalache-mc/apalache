package at.forsyte.apalache.io.annotations

import scala.util.parsing.combinator.JavaTokenParsers
import java.io.{Reader, StringReader}

/**
 * A parser for TLA+ annotations. Use the object TlaAnnotationParser to parser the input.
 *
 * @author Igor Konnov
 */
class TlaAnnotationParser extends JavaTokenParsers {
  def expr: Parser[Any] = "@" ~ ident ~ opt("(" ~ repsep(arg, ",") ~ ")") ^^ {
    case _ ~ name ~ None =>
      new TlaAnnotation(name)

    case _ ~ name ~ Some(_ ~ args ~ _) =>
      val collected = args collect { case a: TlaAnnotationArg => a }
      new TlaAnnotation(name, collected: _*)
  }

  def arg: Parser[Any] = stringArg | intArg | boolArg

  def stringArg: Parser[Any] = stringLiteral ^^ { str => TlaAnnotationString(str.slice(1, str.length - 1)) }

  def intArg: Parser[Any] = wholeNumber ^^ { str => TlaAnnotationInt(str.toInt) }

  def boolArg: Parser[Any] = ident ^^ {
    case "true"  => TlaAnnotationBool(true)
    case "false" => TlaAnnotationBool(false)
  }
}

object TlaAnnotationParser {
  abstract class Result
  case class Success(annotation: TlaAnnotation, length: Int) extends Result
  case class Failure(message: String) extends Result

  private val parser: TlaAnnotationParser = new TlaAnnotationParser

  def parse(reader: Reader): Result = {
    parser.parse(parser.expr, reader) match {
      case parser.Success(annotation: TlaAnnotation, rest) => Success(annotation, rest.offset)
      case parser.Success(res, _)                          => Failure("Expected annotation, found: " + res)
      case parser.Failure(msg, _)                          => Failure(msg)
      case parser.Error(msg, _)                            => Failure(msg)
    }
  }

  def parse(text: String): Result = {
    parse(new StringReader(text))
  }
}
