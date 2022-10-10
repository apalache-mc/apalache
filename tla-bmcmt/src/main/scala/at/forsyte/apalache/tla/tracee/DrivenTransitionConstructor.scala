package at.forsyte.apalache.tla.tracee

import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}
import at.forsyte.apalache.tla.types._
import at.forsyte.apalache.tla.types.tla._
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed
import at.forsyte.apalache.tla.pp.Inliner

/**
 * @author
 *   Jure Kukovec
 */
class DrivenTransitionConstructor(
    tracker: TransformationTracker,
    exs: Map[String, TlaEx]) {

  /**
   * Given a state s as a map x1 -> s.x1, ..., xn -> s.xn, constructs the transition, which points to the state
   * (v1,...,vm), for which vi = Ei[s.x1/x1, ..., s.xn/xn].
   *
   * Concretely, assuming all x1,...,xn are free in Ei, this transition is
   * {{{
   * LET
   *  x1 == s.x1
   *  ...
   *  xn == s.xn
   * IN
   *  /\ v1' = E1
   *  /\ ...
   *  /\ vm' = Em
   * }}}
   */
  def txToState(state: State): TlaEx = {

//    val decls = state.toSeq.map { case (originalStateVar, valueInOriginalTraceState) =>
//      // Turns a state variable v into a nullary operator declaration: v == si.v
//      decl(
//          originalStateVar,
//          unchecked(valueInOriginalTraceState),
//      )
//    }

    val args = exs.toSeq.map { case (varname, ex) =>
      assign(
          prime(
              name(varname, ex.typeTag.asTlaType1())
          ),
          unchecked(ex),
      )
    }

    val rFixed = new ReplaceFixed(tracker)
    val subst = rFixed.withFun {
      case NameEx(name) if state.contains(name) => state(name)
    }

    subst(and(args: _*))

//    val letEx = letIn(and(args: _*), decls: _*)
//
//    letEx
  }

}
