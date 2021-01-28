package at.forsyte.apalache.io.tlc

import java.io.{Reader, StringReader}

import at.forsyte.apalache.io.tlc.config._
import com.typesafe.scalalogging.LazyLogging

import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.NoPosition

/**
  * <p>A parser for the TLC configuration files. For the syntax, see ./docs/tlc-config.md.
  *
  * <p>This parser is built with
  * <a href="https://github.com/scala/scala-parser-combinators">Scala parser combinators</a>.</p>
  *
  * @author Igor Konnov
  */
object TlcConfigParserApalache
    extends Parsers
    with TlcConfigParser
    with LazyLogging {
  override type Elem = TlcConfigToken

  private abstract class ConstBinding
  private case class ConstAssignment(name: String, assignment: ConfigConstExpr)
      extends ConstBinding
  private case class ConstReplacement(name: String, replacement: String)
      extends ConstBinding

  /**
    * Parse a configuration file from a reader.
    * @param reader a reader
    * @return a config on success; throws TlcConfigParseError on failure
    */
  def apply(reader: Reader): TlcConfig = {
    config(new TlcConfigTokenReader(TlcConfigLexer(reader))) match {
      case Success(config: TlcConfig, _) => config
      case Success(_, _) =>
        throw new TlcConfigParseError("Unexpected parse result", NoPosition)
      case Failure(msg, next) => throw new TlcConfigParseError(msg, next.pos)
      case Error(msg, next)   => throw new TlcConfigParseError(msg, next.pos)
    }
  }

  /**
    * Parse a configuration file from a string.
    * @param text a string
    * @return a config on success; throws TlcConfigParseError on failure
    */
  def apply(text: String): TlcConfig = {
    apply(new StringReader(text))
  }

  private def config: Parser[TlcConfig] = {
    phrase(rep1(option)) ^^ { cfgs =>
      cfgs.foldLeft(TlcConfig.empty) { (other, cfg) =>
        other.join(cfg)
      }
    }
  }

  private def option: Parser[TlcConfig] = {
    (constList | constraintList | actionConstraintList
      | initNextSection | specSection | invariantList | propertyList | symmetry | view
      | alias | postcondition | checkDeadlock) ^^ { opt =>
      opt
    }
  }

  private def constList: Parser[TlcConfig] = {
    CONST() ~ rep1(assign | replace) ^^ {
      case _ ~ bindingList =>
        val assignments = bindingList.collect {
          case ConstAssignment(nm, asgn) => nm -> asgn
        }
        val replacements = bindingList.collect {
          case ConstReplacement(nm, repl) => nm -> repl
        }
        TlcConfig.empty
          .addConstAssignments(Map(assignments: _*))
          .addConstReplacements(Map(replacements: _*))
    }
  }

  // SYMMETRY constraints. Ignore.
  private def symmetry: Parser[TlcConfig] = {
    SYMMETRY() ~ ident ^^ {
      case _ ~ name =>
        logger.warn(
          "TLC config option SYMMETRY %s will be ignored".format(name)
        )
        TlcConfig.empty
    }
  }

  // VIEW definition. Ignore.
  private def view: Parser[TlcConfig] = {
    VIEW() ~ ident ^^ {
      case _ ~ name =>
        logger.warn("TLC config option VIEW %s will be ignored".format(name))
        TlcConfig.empty
    }
  }

  // ALIAS definition. Ignore.
  private def alias: Parser[TlcConfig] = {
    ALIAS() ~ ident ^^ {
      case _ ~ name =>
        logger.warn("TLC config option ALIAS %s will be ignored".format(name))
        TlcConfig.empty
    }
  }

  // POSTCONDITION definition. Ignore.
  private def postcondition: Parser[TlcConfig] = {
    POSTCONDITION() ~ ident ^^ {
      case _ ~ name =>
        logger.warn(
          "TLC config option POSTCONDITION %s will be ignored".format(name)
        )
        TlcConfig.empty
    }
  }

  // CHECK_DEADLOCK definition. Ignore.
  private def checkDeadlock: Parser[TlcConfig] = {
    CHECK_DEADLOCK() ~ boolean ^^ {
      case _ ~ flag =>
        logger.warn(
          "TLC config option CHECK_DEADLOCK %b will be ignored".format(flag)
        )
        TlcConfig.empty
    }
  }

  private def assign: Parser[ConstBinding] = {
    ident ~ EQ() ~ constExpr ^^ {
      case IDENT(lhs) ~ _ ~ expr => ConstAssignment(lhs, expr)
    }
  }

  // constant expressions
  private def constExpr: Parser[ConfigConstExpr] = {
    (ident | number | string | (LEFT_BRACE() ~ constExprList ~ RIGHT_BRACE())) ^^ {
      case IDENT(name)  => ConfigModelValue(name)
      case NUMBER(text) => ConfigIntValue(BigInt(text))
      case STRING(text) => ConfigStrValue(text)
      case _ ~ list ~ _ =>
        ConfigSetValue(list.asInstanceOf[List[ConfigConstExpr]]: _*)
    }
  }

  // a comma-separated list of constant expressions
  private def constExprList: Parser[List[ConfigConstExpr]] = {
    repsep(constExpr, COMMA()) ^^ (list => list)
  }

  private def replace: Parser[ConstBinding] = {
    ident ~ LEFT_ARROW() ~ ident ^^ {
      case IDENT(lhs) ~ LEFT_ARROW() ~ IDENT(rhs) => ConstReplacement(lhs, rhs)
    }
  }

  private def constraintList: Parser[TlcConfig] = {
    CONSTRAINT() ~ rep1(ident) ^^ {
      case _ ~ list =>
        val cons = list.collect { case IDENT(name) => name }
        TlcConfig.empty.addStateConstraints(cons)
    }
  }

  private def actionConstraintList: Parser[TlcConfig] = {
    ACTION_CONSTRAINT() ~ rep1(ident) ^^ {
      case _ ~ list =>
        val cons = list.collect { case IDENT(name) => name }
        TlcConfig.empty.addActionConstraints(cons)
    }
  }

  private def initNextSection: Parser[TlcConfig] = {
    (INIT() ~ ident ~ NEXT() ~ ident | NEXT() ~ ident ~ INIT() ~ ident) ^^ {
      case INIT() ~ IDENT(initName) ~ _ ~ IDENT(nextName) =>
        TlcConfig.empty.setBehaviorSpecUnlessNull(
          InitNextSpec(initName, nextName)
        )

      case NEXT() ~ IDENT(nextName) ~ _ ~ IDENT(initName) =>
        TlcConfig.empty.setBehaviorSpecUnlessNull(
          InitNextSpec(initName, nextName)
        )
    }
  }

  private def specSection: Parser[TlcConfig] = {
    SPECIFICATION() ~ ident ^^ {
      case _ ~ IDENT(specName) =>
        TlcConfig.empty.setBehaviorSpecUnlessNull(TemporalSpec(specName))
    }
  }

  private def invariantList: Parser[TlcConfig] = {
    INVARIANT() ~ rep1(ident) ^^ {
      case _ ~ list =>
        val invs = list.collect { case IDENT(name) => name }
        TlcConfig.empty.addInvariants(invs)
    }
  }

  private def propertyList: Parser[TlcConfig] = {
    PROPERTY() ~ rep1(ident) ^^ {
      case _ ~ list =>
        val props = list.collect { case IDENT(name) => name }
        TlcConfig.empty.addTemporalProps(props)
    }
  }

  private def ident: Parser[IDENT] = {
    accept("identifier", { case id @ IDENT(_) => id })
  }

  private def number: Parser[NUMBER] = {
    accept("number", { case n @ NUMBER(_) => n })
  }

  private def string: Parser[STRING] = {
    accept("string", { case n @ STRING(_) => n })
  }

  private def boolean: Parser[BOOLEAN] = {
    accept("boolean", { case n @ BOOLEAN(_) => n })
  }
}
