package at.forsyte.apalache.io.tlc.config

import at.forsyte.apalache.io.tlc.config.ConfigModelValue.STR_PREFIX
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{TlaEx, Typed}
import at.forsyte.apalache.tla.typecheck.TypedPredefs._
import at.forsyte.apalache.tla.typecheck._

import scala.util.parsing.input.NoPosition

/**
 * A behavior spec is either Init-Next, or a temporal specification Init /\ [] [Next]_vars /\ Temporal.
 */
abstract sealed class BehaviorSpec

/**
 * The behavior is given by INIT and NEXT.
 *
 * @param init name of the Init predicate
 * @param next name of the Next predicate
 */
case class InitNextSpec(init: String, next: String) extends BehaviorSpec

/**
 * The behavior is given by SPECIFICATION, that is, a definition of the form Init /\ [] [Next]_vars /\ Temporal.
 *
 * @param name the name of the specification definition
 */
case class TemporalSpec(name: String) extends BehaviorSpec

/**
 * An unspecified behavior spec.
 */
case class NullSpec() extends BehaviorSpec

/**
 * A constant expression that can be written in the right-hand side of an assignment.
 */
abstract sealed class ConfigConstExpr {

  /**
   * Convert the expression to the intermediate representation.
   *
   * @return the TLA IR expression that represents the parsed constant expression
   */
  def toTlaEx: TlaEx
}

object ConfigModelValue {

  /**
   * Every model value is prefixed with this string when converted to a string.
   */
  val STR_PREFIX = "ModelValue_"
}

/**
 * A TLC model value, that is, a unique identifier that is treated as an uninterpreted constant.
 *
 * @param name the name of a model value
 */
case class ConfigModelValue(name: String) extends ConfigConstExpr {
  override def toTlaEx: TlaEx = {
    // currently, we use the type Str for all model values.
    // In the future, we might want to distinguish between different uninterpreted types.
    // See https://github.com/informalsystems/apalache/issues/570
    tla.str(STR_PREFIX + name).typed(StrT1())
  }
}

/**
 * An unbounded integer literal.
 *
 * @param num an integer as BigInt
 */
case class ConfigIntValue(num: BigInt) extends ConfigConstExpr {
  override def toTlaEx: TlaEx = tla.bigInt(num).typed(IntT1())
}

/**
 * A Boolean literal.
 *
 * @param b a boolean
 */
case class ConfigBoolValue(b: Boolean) extends ConfigConstExpr {
  override def toTlaEx: TlaEx = tla.bool(b).typed(BoolT1())
}

/**
 * A string literal.
 *
 * @param str a string
 */
case class ConfigStrValue(str: String) extends ConfigConstExpr {
  override def toTlaEx: TlaEx = tla.str(str).typed(StrT1())
}

/**
 * A set literal.
 *
 * @param elems the set elements, which are constant expression themselves.
 */
case class ConfigSetValue(elems: ConfigConstExpr*) extends ConfigConstExpr {
  override def toTlaEx: TlaEx = {
    val setElems = elems.map(_.toTlaEx)
    if (setElems.isEmpty) {
      // the element type is uknown, introduce a polymorphic type Set(a)
      tla.enumSet().typed(SetT1(VarT1(0)))
    } else {
      // the element type should be unique
      val headType = setElems.head.typeTag.asTlaType1()
      if (setElems.tail.exists(_.typeTag != Typed(headType))) {
        throw new TlcConfigParseError("Set elements have different types: " + setElems.mkString(", "), NoPosition)
      } else {
        tla.enumSet(setElems: _*).typed(SetT1(headType))
      }
    }
  }
}

/**
 * A parsed TLC configuration file. The case class is used here to make copying easier.
 *
 * @param constAssignments  Assignments of the form MyParam = ConstExpr, which makes TLC to replace MyParam with
 *                          the expression.
 * @param constReplacements Replacements of the form MyParam <- AnotherDef. In this case,
 *                          AnotherDef has to be defined in the respective TLA+ module.
 * @param stateConstraints  state constraints
 * @param actionConstraints action constraints
 * @param invariants        A list of invariants to check.
 * @param temporalProps     A list of temporal properties to check.
 * @param behaviorSpec      A behavior specification. A well-formed config should have one.
 * @author Igor Konnov
 */
case class TlcConfig(constAssignments: Map[String, ConfigConstExpr], constReplacements: Map[String, String],
    stateConstraints: List[String], actionConstraints: List[String], invariants: List[String],
    temporalProps: List[String], behaviorSpec: BehaviorSpec) {

  def addConstAssignments(moreConstAssignments: Map[String, ConfigConstExpr]): TlcConfig = {
    this.copy(constAssignments = constAssignments ++ moreConstAssignments)
  }

  def addConstReplacements(moreConstReplacements: Map[String, String]): TlcConfig = {
    this.copy(constReplacements = constReplacements ++ moreConstReplacements)
  }

  def addStateConstraints(moreStateConstraints: List[String]): TlcConfig = {
    this.copy(stateConstraints = stateConstraints ++ moreStateConstraints)
  }

  def addActionConstraints(moreActionConstraints: List[String]): TlcConfig = {
    this.copy(actionConstraints = actionConstraints ++ moreActionConstraints)
  }

  def addInvariants(moreInvariants: List[String]): TlcConfig = {
    this.copy(invariants = invariants ++ moreInvariants)
  }

  def addTemporalProps(moreTemporalProps: List[String]): TlcConfig = {
    this.copy(temporalProps = temporalProps ++ moreTemporalProps)
  }

  def setBehaviorSpecUnlessNull(newSpec: BehaviorSpec): TlcConfig = {
    if (behaviorSpec != NullSpec() && newSpec != NullSpec()) {
      throw new TlcConfigParseError(
          "Found several behavior specifications: %s and %s"
            .format(behaviorSpec, newSpec), NoPosition)
    }

    if (newSpec != NullSpec()) {
      this.copy(behaviorSpec = newSpec)
    } else {
      this
    }
  }

  def join(other: TlcConfig): TlcConfig = {
    this
      .addConstReplacements(other.constReplacements)
      .addConstAssignments(other.constAssignments)
      .addStateConstraints(other.stateConstraints)
      .addActionConstraints(other.actionConstraints)
      .addInvariants(other.invariants)
      .addTemporalProps(other.temporalProps)
      .setBehaviorSpecUnlessNull(other.behaviorSpec)
  }
}

object TlcConfig {
  val empty: TlcConfig =
    TlcConfig(constAssignments = Map(), constReplacements = Map(), stateConstraints = List.empty,
        actionConstraints = List.empty, invariants = List.empty, temporalProps = List.empty, behaviorSpec = NullSpec())
}
