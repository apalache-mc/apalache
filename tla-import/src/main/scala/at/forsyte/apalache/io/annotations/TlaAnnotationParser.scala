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

object TlaAnnotationParser extends TlaAnnotationParser {
  def apply(reader: Reader): TlaAnnotation = {
    parseAll(expr, reader) match {
      case Success(annotation: TlaAnnotation, _) => annotation
      case Success(res, _)                       => throw new TlaAnnotationParserError("Expected annotation, found: " + res)
      case Failure(msg, _)                       => throw new TlaAnnotationParserError(msg)
      case Error(msg, _)                         => throw new TlaAnnotationParserError(msg)
    }
  }

  def apply(text: String): TlaAnnotation = {
    this(new StringReader(text))
  }
}
