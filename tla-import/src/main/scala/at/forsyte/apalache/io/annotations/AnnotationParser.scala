package at.forsyte.apalache.io.annotations

import scala.util.parsing.combinator.JavaTokenParsers
import java.io.{Reader, StringReader}

/**
 * A parser for TLA+ annotations. Use the object TlaAnnotationParser to parser the input.
 *
 * @author Igor Konnov
 */
class AnnotationParser extends JavaTokenParsers {
  def expr: Parser[Any] = "@" ~ ident ~ opt(argsInParentheses | argAfterColon) ^^ {
    case _ ~ name ~ None =>
      new Annotation(name)

    case _ ~ name ~ Some(args) =>
      new Annotation(name, args: _*)
  }

  def argsInParentheses: Parser[List[AnnotationArg]] = "(" ~ repsep(arg, ",") ~ ")" ^^ { case _ ~ args ~ _ =>
    args
  }

  def argAfterColon: Parser[List[AnnotationArg]] = ":" ~ nonSemiString ~ ";" ^^ { case _ ~ str ~ _ =>
    List(AnnotationString(str))
  }

  def arg: Parser[AnnotationArg] = stringArg | intArg | boolArg

  def stringArg: Parser[AnnotationString] = stringLiteral ^^ { str =>
    AnnotationString(str.slice(1, str.length - 1))
  }

  def intArg: Parser[AnnotationInt] = wholeNumber ^^ { str =>
    AnnotationInt(str.toInt)
  }

  def boolArg: Parser[AnnotationBool] = ident ^^ {
    case "true"  => AnnotationBool(true)
    case "false" => AnnotationBool(false)
  }

  def nonSemiString: Parser[String] = """[^;]*""".r
}

object AnnotationParser {
  abstract class Result
  case class Success(annotation: Annotation, length: Int) extends Result
  case class Failure(message: String) extends Result

  private val parser: AnnotationParser = new AnnotationParser

  def parse(reader: Reader): Result = {
    parser.parse(parser.expr, reader) match {
      case parser.Success(annotation: Annotation, rest) =>
        Success(annotation, rest.offset)
      case parser.Success(res, _) =>
        Failure("Expected annotation, found: " + res)
      case parser.Failure(msg, _) => Failure(msg)
      case parser.Error(msg, _)   => Failure(msg)
    }
  }

  def parse(text: String): Result = {
    parse(new StringReader(text))
  }
}
