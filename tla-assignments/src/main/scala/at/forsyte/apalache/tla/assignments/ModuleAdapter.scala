package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._

/**
 * Moving away from SpecWithTransitions ModuleManipulator allows us to re-insert special TlaEx
 * back into a TlaModule, as operators with special names. All such operators are suffixed with
 * `suffix`, which is a string disallowed by the TLA+ operator naming rules.
 *
 * @author Jure Kukovec
 */
object ModuleAdapter {
  def exprToOperDef(name: String, expr: TlaEx): TlaOperDecl = {
    expr.typeTag match {
      case Typed(tt: TlaType1) =>
        TlaOperDecl(name, List(), expr)(Typed(OperT1(Seq(), tt)))

      case _ =>
        TlaOperDecl(name, List(), expr)(Untyped())
    }
  }

  def exprsToOperDefs(operPrefix: String, transitions: Seq[TlaEx]): Seq[TlaOperDecl] =
    transitions.zipWithIndex map { case (transExpr, index) =>
      // Name + $ + index is guaranteed to not clash with existing names, as
      // $ is not an allowed symbol in TLA.
      // We pad the number to 4 digits, so it is easy to sort them.
      exprToOperDef("%s%04d".format(operPrefix, index), transExpr)
    }

  def declsFromTransitions(transitionOperName: String, transitions: Seq[SymbTrans]): Seq[TlaOperDecl] =
    // drop selections because of lacking implementation further on
    exprsToOperDefs(transitionOperName,
        transitions map {
      _._2
    })

  def insertTransitions(module: TlaModule, transitionOperName: String, transitions: Seq[SymbTrans]): TlaModule = {
    new TlaModule(module.name, declsFromTransitions(transitionOperName, transitions) ++ module.declarations)
  }

  /**
   * After re-inserting the transitions into the spec as operators with special names,
   * we want to extract them again when we need them. We know all symbolic transition names
   * (for init or next, depending on `baseName`) contain the `SymbolicTransitionInserter.suffix`
   * string, that distinguishes them from normal operators.
   */
  def getTransitionsFromSpec(module: TlaModule, prefix: String): Seq[TlaEx] =
    module.operDeclarations
      .filter {
        _.name.startsWith(prefix) // transitions end in 0,1,...
      }
      .sortBy(_.name)
      .map {
        _.body
      }

  def getOperatorOption(module: TlaModule, name: String): Option[TlaEx] =
    module.operDeclarations.find {
      _.name == name
    } map {
      _.body
    }
}
