package at.forsyte.apalache.io.tlc.config

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
  * A parsed TLC configuration file. The case class is used here to make copying easier.
  *
  * @param constAssignments  Assignments of the form MyParam = ModelValue, which makes TLC to replace MyParam with
  *                          a model value. Although TLC supports other kinds of values, e.g., 1, "foo", { 1, 2, 3 },
  *                          we do not like to write a complex parser.
  *                          Use a replacement, if you have richer expressions.
  * @param constReplacements Replacements of the form MyParam <- AnotherDef. In this case,
  *                          AnotherDef has to be defined in the respective TLA+ module.
  *
  * @param stateConstraints state constraints
  * @param actionConstraints action constraints
  * @param invariants A list of invariants to check.
  *
  * @param temporalProps A list of temporal properties to check.
  *
  * @param behaviorSpec A behavior specification. A well-formed config should have one.
  *
  * @author Igor Konnov
  */
case class TlcConfig(constAssignments: Map[String, String],
                     constReplacements: Map[String, String],
                     stateConstraints: List[String],
                     actionConstraints: List[String],
                     invariants: List[String] = List(),
                     temporalProps: List[String],
                     behaviorSpec: BehaviorSpec)
