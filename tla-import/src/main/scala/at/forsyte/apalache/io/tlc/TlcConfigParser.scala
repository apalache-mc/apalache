package at.forsyte.apalache.io.tlc

import java.io.{Reader, StringReader}

import at.forsyte.apalache.io.tlc.config._

import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.NoPosition


/**
  * <p>A parser for the TLC configuration files. For the syntax,
  * see [<a href="http://research.microsoft.com/users/lamport/tla/book.html">Specifying Systems</a>, Ch. 14]
  * by Leslie Lamport. TLC configuration files have a rich assignment syntax, e.g., one can write a parameter assignment
  * `S = {{1, 2, 3}, "a"}`. We ignore this syntax, as TLA Toolbox produces configuration files using the replacement
  * syntax `S <- const...`. The only exception is when one uses model values, e.g., `S = S`, which we also support.</p>
  *
  * <p>This parser is built using
  * <a href="https://github.com/scala/scala-parser-combinators">Scala parser combinators</a>.</p>
  *
  * @author Igor Konnov
  */
object TlcConfigParser extends Parsers {
  override type Elem = TlcConfigToken

  private abstract class ConstBinding
  private case class ConstAssignment(name: String, assignment: String) extends ConstBinding
  private case class ConstReplacement(name: String, replacement: String) extends ConstBinding

  /**
    * Parse a configuration file from a reader.
    * @param reader a reader
    * @return a config on success; throws TlcConfigParseError on failure
    */
  def apply(reader: Reader): TlcConfig = {
    config(new TlcConfigTokenReader(TlcConfigLexer(reader))) match {
      case Success(config: TlcConfig, _) => config
      case Success(_, _) => throw new TlcConfigParseError("Unexpected parse result", NoPosition)
      case Failure(msg, next) => throw new TlcConfigParseError(msg, next.pos)
      case Error(msg, next) => throw new TlcConfigParseError(msg, next.pos)
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

  // the access point
  private def config: Parser[TlcConfig] = {
    phrase(allConstLists ~ allConstraintLists ~ allActionConstraintLists ~
        (initNextSection | specSection) ~ allInvariantLists ~ allPropertyLists) ^^ {
      case consts ~ stateConstraints ~ actionConstraints ~ spec ~ invariants ~ properties =>
        val assignments = consts.collect { case ConstAssignment(nm, asgn) => nm -> asgn }
        val replacements = consts.collect { case ConstReplacement(nm, repl) => nm -> repl }
        TlcConfig(
          constAssignments = Map(assignments :_*),
          constReplacements = Map(replacements :_*),
          stateConstraints = stateConstraints,
          actionConstraints = actionConstraints,
          invariants = invariants,
          temporalProps = properties,
          spec)
    }
  }

  private def allConstLists: Parser[List[ConstBinding]] = {
    rep(constList | symmetryHint) ^^ {
      lists => lists.flatten
    }
  }

  private def constList: Parser[List[ConstBinding]] = {
    CONST() ~ rep1(assign | replace) ^^ {
      case _ ~ bindingList => bindingList
    }
  }

  // Constants can come with SYMMETRY definitions. The parser just swallows them.
  private def symmetryHint: Parser[List[ConstBinding]] = {
    SYMMETRY() ~ ident ^^ {
      case _ ~ _ => List() // ignore the SYMMETRY definitions
    }
  }

  private def assign: Parser[ConstBinding] = {
    ident ~ EQ() ~ (ident|number) ^^ {
      case IDENT(lhs) ~ EQ() ~ IDENT(rhs) => ConstAssignment(lhs, rhs)
      case IDENT(lhs) ~ EQ() ~ NUMBER(rhs) => ConstAssignment(lhs, rhs)
    }
  }

  private def replace: Parser[ConstBinding] = {
    ident ~ LEFT_ARROW() ~ ident ^^ {
      case IDENT(lhs) ~ LEFT_ARROW() ~ IDENT(rhs) => ConstReplacement(lhs, rhs)
    }
  }

  private def allConstraintLists: Parser[List[String]] = {
    rep(constraintList) ^^ {
      lists => lists.flatten
    }
  }

  private def constraintList: Parser[List[String]] = {
    CONSTRAINT() ~ rep1(ident) ^^ {
      case _ ~ list => list.collect { case IDENT(name) => name }
    }
  }

  private def allActionConstraintLists: Parser[List[String]] = {
    rep(actionConstraintList) ^^ {
      lists => lists.flatten
    }
  }

  private def actionConstraintList: Parser[List[String]] = {
    ACTION_CONSTRAINT() ~ rep1(ident) ^^ {
      case _ ~ list => list.collect { case IDENT(name) => name }
    }
  }

  private def initNextSection: Parser[BehaviorSpec] = {
    INIT() ~ ident ~ NEXT() ~ ident ^^ {
      case _ ~ IDENT(initName) ~ _ ~ IDENT(nextName) => InitNextSpec(initName, nextName)
    }
  }

  private def specSection: Parser[BehaviorSpec] = {
    SPECIFICATION() ~ ident ^^ {
      case _ ~ IDENT(specName) => TemporalSpec(specName)
    }
  }

  private def allInvariantLists: Parser[List[String]] = {
    rep(invariantList) ^^ {
      lists => lists.flatten
    }
  }

  private def invariantList: Parser[List[String]] = {
    INVARIANT() ~ rep1(ident) ^^ {
      case _ ~ list => list.collect { case IDENT(name) => name }
    }
  }

  private def allPropertyLists: Parser[List[String]] = {
    rep(propertyList) ^^ {
      lists => lists.flatten
    }
  }

  private def propertyList: Parser[List[String]] = {
    PROPERTY() ~ rep1(ident) ^^ {
      case _ ~ list => list.collect { case IDENT(name) => name }
    }
  }

  private def ident: Parser[IDENT] = {
    accept("identifier", { case id @ IDENT(_) => id })
  }

  private def number: Parser[NUMBER] = {
    accept("number", { case n @ NUMBER(_) => n })
  }
}
