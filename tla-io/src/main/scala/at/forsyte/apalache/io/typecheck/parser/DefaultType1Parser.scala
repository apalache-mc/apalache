package at.forsyte.apalache.io.typecheck.parser

import at.forsyte.apalache.tla.lir._

import java.io.StringReader
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
 * @author Igor Konnov
 */
object DefaultType1Parser extends Parsers with Type1Parser {
  override type Elem = Type1Token

  /**
   * Parse a type from a string, possibly substituting aliases with types.
   *
   * @param text a string
   * @return a type on success; throws TlcConfigParseError on failure
   */
  override def parseType(text: String): TlaType1 = {
    closedTypeExpr(new Type1TokenReader(Type1Lexer(new StringReader(text)))) match {
      case Success(result: TlaType1, _) => result
      case Success(_, _)                => throw new Type1ParseError("Unexpected parse result", NoPosition)
      case Failure(msg, next)           => throw new Type1ParseError(msg, next.pos)
      case Error(msg, next)             => throw new Type1ParseError(msg, next.pos)
    }
  }

  /**
   * Parse a type alias from a string
   *
   * @param text a string
   * @return an alias name and a type on success; throws Type1ParseError on failure
   */
  override def parseAlias(text: String): (String, TlaType1) = {
    closedAliasExpr(new Type1TokenReader(Type1Lexer(new StringReader(text)))) match {
      case Success((name, tt: TlaType1), _) => (name, tt)
      case Success(_, _)                    => throw new Type1ParseError("Unexpected parse result", NoPosition)
      case Failure(msg, next)               => throw new Type1ParseError(msg, next.pos)
      case Error(msg, next)                 => throw new Type1ParseError(msg, next.pos)
    }
  }

  // the access point to the alias parser
  private def closedAliasExpr: Parser[(String, TlaType1)] = phrase(aliasExpr)

  // the access point to the type parser
  private def closedTypeExpr: Parser[TlaType1] = phrase(typeExpr) ^^ (e => e)

  private def aliasExpr: Parser[(String, TlaType1)] = {
    (typeConst ~ EQ() ~ typeExpr) ^^ { case ConstT1(name) ~ _ ~ tt =>
      (name, tt)
    }
  }

  private def typeExpr: Parser[TlaType1] = {
    // functions are tricky, as they start as other expressions, so we have to distinguish them by RIGHT_ARROW
    (noFunExpr ~ opt((RIGHT_ARROW() | DOUBLE_RIGHT_ARROW()) ~ typeExpr)) ^^ {
      case (lhs :: Nil) ~ Some(RIGHT_ARROW() ~ rhs)   => FunT1(lhs, rhs)
      case (lhs :: Nil) ~ None                        => lhs
      case args ~ Some(DOUBLE_RIGHT_ARROW() ~ result) => OperT1(args, result)
    }
  }

  // A type expression. We wrap it with a list, as (type, ..., type) may start an operator type
  private def noFunExpr: Parser[List[TlaType1]] = {
    (INT() | REAL() | BOOL() | STR() | typeVar | typeConst
      | set | seq | tuple | sparseTuple
      | record | parenExpr) ^^ {
      case INT()        => List(IntT1())
      case REAL()       => List(RealT1())
      case BOOL()       => List(BoolT1())
      case STR()        => List(StrT1())
      case tt: TlaType1 => List(tt)
      case lst: List[TlaType1] =>
        lst
    }
  }

  // A type or partial type in parenthesis.
  // We can have: (), (type), or (type, ..., type). All of them work as a left-hand side of an operator type.
  // Additionally, (type) may just wrap a type such as in (A -> B) -> C.
  // Thus, return a list here, and resolve it in the rules above.
  private def parenExpr: Parser[List[TlaType1]] = {
    (LPAREN() ~ repsep(typeExpr, COMMA()) ~ RPAREN()) ^^ { case _ ~ list ~ _ =>
      list
    }
  }

  // a set type like Set(Int)
  private def set: Parser[TlaType1] = {
    SET() ~ LPAREN() ~ typeExpr ~ RPAREN() ^^ { case _ ~ _ ~ elemType ~ _ =>
      SetT1(elemType)
    }
  }

  // a sequence type like Seq(Int)
  private def seq: Parser[TlaType1] = {
    SEQ() ~ LPAREN() ~ typeExpr ~ RPAREN() ^^ { case _ ~ _ ~ elemType ~ _ =>
      SeqT1(elemType)
    }
  }

  // a tuple type like <<Int, Bool>>
  private def tuple: Parser[TlaType1] = {
    DOUBLE_LEFT_ANGLE() ~ rep1sep(typeExpr, COMMA()) ~ DOUBLE_RIGHT_ANGLE() ^^ { case _ ~ list ~ _ =>
      TupT1(list: _*)
    }
  }

  // a sparse tuple type like {3: Int, 5: Bool}
  private def sparseTuple: Parser[TlaType1] = {
    LCURLY() ~ repsep(typedFieldNo, COMMA()) ~ RCURLY() ^^ { case _ ~ list ~ _ =>
      SparseTupT1(SortedMap(list: _*))
    }
  }

  // a single component of a sparse tuple, e.g., 3: Int
  private def typedFieldNo: Parser[(Int, TlaType1)] = {
    fieldNo ~ COLON() ~ typeExpr ^^ { case FIELD_NO(no) ~ _ ~ fieldType =>
      (no, fieldType)
    }
  }

  // a field number in a sparse tuple, like 3
  private def fieldNo: Parser[FIELD_NO] = {
    accept("field number", { case f @ FIELD_NO(_) =>
      f
    })
  }

  // a record type like [a: Int, b: Bool]
  private def record: Parser[TlaType1] = {
    LBRACKET() ~ repsep(typedField, COMMA()) ~ RBRACKET() ^^ { case _ ~ list ~ _ =>
      RecT1(SortedMap(list: _*))
    }
  }

  // a single component of record type, e.g., a: Int
  private def typedField: Parser[(String, TlaType1)] = {
    fieldName ~ COLON() ~ typeExpr ^^ { case IDENT(name) ~ _ ~ fieldType =>
      (name, fieldType)
    }
  }

  // A record field name, like foo_BAR2.
  // As field name are colliding with CAPS_IDENT and TYPE_VAR, we expect all of them.
  private def fieldName: Parser[IDENT] = {
    accept("field name", { case f @ IDENT(_) =>
      f
    })
  }

  // a type variable, e.g., c
  private def typeVar: Parser[VarT1] = {
    accept("typeVar", { case IDENT(name) if VarT1.isValidName(name) => VarT1(name) })
  }

  // a type constant or an alias name, e.g., BAZ
  private def typeConst: Parser[ConstT1] = {
    acceptMatch("typeConst", { case IDENT(name) if (name.toUpperCase() == name) => ConstT1(name) })
  }
}
