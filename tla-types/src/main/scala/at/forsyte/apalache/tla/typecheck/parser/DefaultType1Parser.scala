package at.forsyte.apalache.tla.typecheck.parser

import java.io.{Reader, StringReader}

import at.forsyte.apalache.tla.typecheck._

import scala.collection.immutable.SortedMap
import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.NoPosition

/**
  * <p>A parser for the expressions in Type System 1. This parser happened to be harder to write, as the straightforward
  * parsing of function and operator types leads to ambiguities. This parser is hand-written with the help of
  * Scala parser combinators. For small grammars such as this one this is a better choice in terms of long-term support
  * than a parser generator.</p>
  *
  * <p><b>Warning:</b> Avoid using this object directly. Rather use Type1ParserFactory.</p>
  *
  * @see at.forsyte.apalache.tla.typecheck.Type1ParserFactory
  *
  * @author Igor Konnov
  */
object DefaultType1Parser extends Parsers with Type1Parser {
  override type Elem = Type1Token

  /**
    * Parse a type from a string.
    *
    * @param text a string
    * @return a type on success; throws Type1ParseError on failure
    */
  def apply(text: String): TlaType1 = {
    apply(new StringReader(text))
  }

  /**
    * Parse a type file from a reader.
    * @param reader a reader
    * @return a typeExpr on success; throws Type1ParseError on failure
    */
  def apply(reader: Reader): TlaType1 = {
    closedTypeExpr(new Type1TokenReader(Type1Lexer(reader))) match {
      case Success(result: TlaType1, _) => result
      case Success(_, _) => throw new Type1ParseError("Unexpected parse result", NoPosition)
      case Failure(msg, next) => throw new Type1ParseError(msg, next.pos)
      case Error(msg, next) => throw new Type1ParseError(msg, next.pos)
    }
  }

  // the access point
  private def closedTypeExpr: Parser[TlaType1] = phrase(typeExpr) ^^ (e => e)

  private def typeExpr: Parser[TlaType1] = {
    // functions are tricky, as they start as other expressions, so we have to distinguish them by RIGHT_ARROW
    (noFunExpr ~ opt((RIGHT_ARROW() | DOUBLE_RIGHT_ARROW()) ~ typeExpr)) ^^ {
      case (lhs :: Nil) ~ Some(RIGHT_ARROW() ~ rhs) => FunT1(lhs, rhs)
      case (lhs :: Nil) ~ None => lhs
      case args ~ Some(DOUBLE_RIGHT_ARROW() ~ result) => OperT1(args, result)
    }
  }

  // A type expression. We wrap it with a list, as (type, ..., type) may start an operator type
  private def noFunExpr: Parser[List[TlaType1]] = {
    (INT() | REAL() | BOOL() | STR() | typeVar | typeConst | set | seq | tuple | record | parenExpr) ^^ {
      case INT() => List(IntT1())
      case REAL() => List(RealT1())
      case BOOL() => List(BoolT1())
      case STR() => List(StrT1())
      case FIELD_IDENT(name) => List(VarT1(name))
      case CAPS_IDENT(name) => List(ConstT1(name))
      case s @ SetT1(_) => List(s)
      case s @ SeqT1(_) => List(s)
      case f @ FunT1(_, _) => List(f)
      case t @ TupT1(_*) => List(t)
      case r @ RecT1(_) => List(r)
      case lst: List[TupT1] => lst
    }
  }

  // A type or partial type in parenthesis.
  // We can have: (), (type), or (type, ..., type). All of them work as a left-hand side of an operator type.
  // Additionally, (type) may just wrap a type such as in (A -> B) -> C.
  // Thus, return a list here, and resolve it in the rules above.
  private def parenExpr: Parser[List[TlaType1]] = {
    (LPAREN() ~ repsep(typeExpr, COMMA()) ~ RPAREN()) ^^ {
      case _ ~ list ~ _ => list
    }
  }

  // a set type like Set(Int)
  private def set: Parser[TlaType1] = {
    SET() ~ LPAREN() ~ typeExpr ~ RPAREN() ^^ {
      case _ ~ _ ~ elemType ~ _ => SetT1(elemType)
    }
  }

  // a sequence type like Seq(Int)
  private def seq: Parser[TlaType1] = {
    SEQ() ~ LPAREN() ~ typeExpr ~ RPAREN() ^^ {
      case _ ~ _ ~ elemType ~ _ => SeqT1(elemType)
    }
  }

  // a tuple type like <<Int, Bool>>
  private def tuple: Parser[TlaType1] = {
    DOUBLE_LEFT_ANGLE() ~ rep1sep(typeExpr, COMMA()) ~ DOUBLE_RIGHT_ANGLE() ^^ {
      case _ ~ list ~ _ => TupT1(list :_*)
    }
  }

  // a record type like [a: Int, b: Bool]
  private def record: Parser[TlaType1] = {
    LBRACKET() ~ rep1sep(typedField, COMMA()) ~ RBRACKET() ^^ {
      case _ ~ list ~ _ =>
        RecT1(SortedMap(list :_*))
    }
  }

  // a single component of record type, e.g., a: Int
  private def typedField: Parser[(String, TlaType1)] = {
    fieldName ~ COLON() ~ typeExpr ^^ {
      case FIELD_IDENT(name) ~ _ ~ fieldType => (name, fieldType)
    }
  }

  // a record field name, like foo_BAR2
  private def fieldName: Parser[FIELD_IDENT] = {
    accept("field name", {
      case f @ FIELD_IDENT(_) => f
      case CAPS_IDENT(name) => FIELD_IDENT(name)
    })
  }

  // a type variable, e.g., c
  private def typeVar: Parser[FIELD_IDENT] = {
    accept("typeVar", { case id @ FIELD_IDENT(_) => id })
  }

  // a type constant, e.g., BAZ
  private def typeConst: Parser[CAPS_IDENT] = {
    accept("typeConst", { case id @ CAPS_IDENT(_) => id })
  }

}
