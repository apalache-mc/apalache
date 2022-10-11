package at.forsyte.apalache.tla.tracee

import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}
import at.forsyte.apalache.tla.types.tla._
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed

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
   *  /\ v1' = E1[...]
   *  /\ ...
   *  /\ vm' = Em[...]
   * }}}
   */
  def txToState(state: State): TlaEx = {

    // Set up the expressions vi' = Ei (without substitution)
    val args = exs.toSeq.map { case (varname, ex) =>
      assign(
          prime(
              name(varname, ex.typeTag.asTlaType1())
          ),
          unchecked(ex),
      )
    }

    // Apply the derived substitution to the and-conjoined arguments
    new ReplaceFixed(tracker).withFun {
      case NameEx(name) if state.contains(name) => state(name)
    }(and(args: _*))
  }

}
