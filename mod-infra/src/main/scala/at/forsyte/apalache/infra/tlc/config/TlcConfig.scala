package at.forsyte.apalache.infra.tlc.config

import at.forsyte.apalache.infra.tlc.config.ConfigModelValue.STR_PREFIX
import at.forsyte.apalache.tla.lir.{TlaType1, Typed, VarT1}
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.{tla, ModelValueHandler}

import scala.util.parsing.input.NoPosition

/**
 * A behavior spec is either Init-Next, or a temporal specification Init /\ [] [Next]_vars /\ Temporal.
 */
sealed abstract class BehaviorSpec

/**
 * The behavior is given by INIT and NEXT.
 *
 * @param init
 *   name of the Init predicate
 * @param next
 *   name of the Next predicate
 */
case class InitNextSpec(init: String, next: String) extends BehaviorSpec

/**
 * The behavior is given by SPECIFICATION, that is, a definition of the form Init /\ [] [Next]_vars /\ Temporal.
 *
 * @param name
 *   the name of the specification definition
 */
case class TemporalSpec(name: String) extends BehaviorSpec

/**
 * An unspecified behavior spec.
 */
case class NullSpec() extends BehaviorSpec

/**
 * A constant expression that can be written in the right-hand side of an assignment.
 */
sealed abstract class ConfigConstExpr {

  /**
   * Convert the expression to the intermediate representation.
   *
   * @return
   *   the TLA IR expression that represents the parsed constant expression
   */
  def toTla: TBuilderInstruction
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
 * @param name
 *   the name of a model value
 */
case class ConfigModelValue(name: String) extends ConfigConstExpr {
  override def toTla: TBuilderInstruction = {
    // currently, we use the type Str for all model values.
    // In the future, we might want to distinguish between different uninterpreted types.
    // See https://github.com/informalsystems/apalache/issues/570
    tla.str(STR_PREFIX + name)
  }
}

/**
 * An unbounded integer literal.
 *
 * @param num
 *   an integer as BigInt
 */
case class ConfigIntValue(num: BigInt) extends ConfigConstExpr {
  override def toTla: TBuilderInstruction = tla.int(num)
}

/**
 * A Boolean literal.
 *
 * @param b
 *   a boolean
 */
case class ConfigBoolValue(b: Boolean) extends ConfigConstExpr {
  override def toTla: TBuilderInstruction = tla.bool(b)
}

/**
 * A string literal.
 *
 * @param str
 *   a string
 */
case class ConfigStrValue(str: String) extends ConfigConstExpr {
  override def toTla: TBuilderInstruction = {
    ModelValueHandler.typeAndIndex(str) match {
      case None                => tla.str(str)
      case Some((constT, idx)) => tla.const(idx, constT)
    }

  }
}

/**
 * A set literal.
 *
 * @param elems
 *   the set elements, which are constant expression themselves.
 */
case class ConfigSetValue(elems: ConfigConstExpr*) extends ConfigConstExpr {
  override def toTla: TBuilderInstruction = {
    val setElems = elems.map(_.toTla)
    if (setElems.isEmpty) {
      // the element type is uknown, introduce a polymorphic type Set(a)
      tla.emptySet(VarT1(0))
    } else {
      // the element type should be unique
      val headType = TlaType1.fromTypeTag(setElems.head.typeTag)
      if (setElems.tail.exists(_.typeTag != Typed(headType))) {
        throw new TlcConfigParseError("Set elements have different types: " + setElems.mkString(", "), NoPosition)
      } else {
        tla.enumSet(setElems: _*)
      }
    }
  }
}

/**
 * A parsed TLC configuration file. The case class is used here to make copying easier.
 *
 * @param constAssignments
 *   Assignments of the form MyParam = ConstExpr, which makes TLC to replace MyParam with the expression.
 * @param constReplacements
 *   Replacements of the form MyParam <- AnotherDef. In this case, AnotherDef has to be defined in the respective TLA+
 *   module.
 * @param stateConstraints
 *   state constraints
 * @param actionConstraints
 *   action constraints
 * @param invariants
 *   A list of invariants to check.
 * @param temporalProps
 *   A list of temporal properties to check.
 * @param behaviorSpec
 *   A behavior specification. A well-formed config should have one.
 * @author
 *   Igor Konnov
 */
case class TlcConfig(
    constAssignments: Map[String, ConfigConstExpr],
    constReplacements: Map[String, String],
    stateConstraints: List[String],
    actionConstraints: List[String],
    invariants: List[String],
    temporalProps: List[String],
    behaviorSpec: BehaviorSpec) {

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
      throw new TlcConfigParseError("Found several behavior specifications: %s and %s"
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
    TlcConfig(
        constAssignments = Map(),
        constReplacements = Map(),
        stateConstraints = List.empty,
        actionConstraints = List.empty,
        invariants = List.empty,
        temporalProps = List.empty,
        behaviorSpec = NullSpec(),
    )
}
