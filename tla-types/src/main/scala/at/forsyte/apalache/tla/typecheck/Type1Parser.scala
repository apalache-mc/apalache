package at.forsyte.apalache.tla.typecheck

import java.io.{Reader, StringReader}

import at.forsyte.apalache.tla.typecheck.parser._
import pcal.MappingObject.RightParen

import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.NoPosition

object Type1Parser extends Parsers {
  override type Elem = Type1Token


  /**
    * Parse a configuration file from a reader.
    * @param reader a reader
    * @return a typeExpr on success; throws TlcConfigParseError on failure
    */
  def apply(reader: Reader): TlaType1 = {
    closedTypeExpr(new Type1TokenReader(Type1Lexer(reader))) match {
      case Success(result: TlaType1, _) => result
      case Success(_, _) => throw new Type1ParseError("Unexpected parse result", NoPosition)
      case Failure(msg, next) => throw new Type1ParseError(msg, next.pos)
      case Error(msg, next) => throw new Type1ParseError(msg, next.pos)
    }
  }

  /**
    * Parse a configuration file from a string.
    * @param text a string
    * @return a type on success; throws TlcConfigParseError on failure
    */
  def apply(text: String): TlaType1 = {
    apply(new StringReader(text))
  }

  // the access point
  private def closedTypeExpr: Parser[TlaType1] = phrase(typeExpr) ^^ (e => e)

  private def typeExpr: Parser[TlaType1] = {
    (rep(LPAREN()) ~ funExpr ~ rep(RPAREN())) ^^ {
      case _ ~ fe ~ _ => fe
    }
  }

  private def funExpr: Parser[TlaType1] = {
    // functions are tricky, as they start as other expressions, so we have to distinguish them by RIGHT_ARROW
    (noFunExpr ~ opt(RIGHT_ARROW() ~ typeExpr)) ^^ {
      case lt ~ Some(_ ~ rt) => FunT1(lt, rt)
      case lt ~ None => lt
    }
  }

  // a type expression
  private def noFunExpr: Parser[TlaType1] = {
    (INT() | BOOL() | STR() | typeVar | typeConst | set | seq) ^^ {
      case INT() => IntT1()
      case BOOL() => BoolT1()
      case STR() => StrT1()
      case LETTER_IDENT(name) => VarT1(name)
      case CAPS_IDENT(name) => ConstT1(name)
      case s @ SetT1(_) => s
      case s @ SeqT1(_) => s
    }
  }

  private def set: Parser[TlaType1] = {
    SET() ~ LPAREN() ~ typeExpr ~ RPAREN() ^^ {
      case _ ~ _ ~ elemType ~ _ => SetT1(elemType)
    }
  }

  private def seq: Parser[TlaType1] = {
    SEQ() ~ LPAREN() ~ typeExpr ~ RPAREN() ^^ {
      case _ ~ _ ~ elemType ~ _ => SeqT1(elemType)
    }
  }

  private def fun: Parser[TlaType1] = {
    typeExpr ~ RIGHT_ARROW() ~ typeExpr ^^ {
      case argType ~ _ ~ resType => FunT1(argType, resType)
    }
  }

  private def typeVar: Parser[LETTER_IDENT] = {
    accept("typeVar", { case id @ LETTER_IDENT(_) => id })
  }

  private def typeConst: Parser[CAPS_IDENT] = {
    accept("typeConst", { case id @ CAPS_IDENT(_) => id })
  }

}
