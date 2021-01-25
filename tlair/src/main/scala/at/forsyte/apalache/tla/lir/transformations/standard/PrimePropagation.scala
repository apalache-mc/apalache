package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.transformations.{
  TlaExTransformation,
  TransformationTracker
}
import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaEx}

/**
  * A reference implementation of an expression transformer. It expands the prime operator,
  * that is, when it meets an expression e', it propagates primes inside e.
  *
  * @param stateVars state variables
  * @param tracker a transformation tracker
  */
class PrimePropagation(tracker: TransformationTracker, stateVars: Set[String])
    extends TlaExTransformation {

  /**
    * Propagate primes in the expression to the state variables.
    * All names that are different from state variables should subsume prime.
    *
    * @param expr an expression to propagate primes
    * @return the expression where primes are propagated to the level of state variables
    */
  override def apply(expr: TlaEx): TlaEx = {
    def transform(primeToAdd: Boolean): TlaEx => TlaEx =
      tracker.trackEx {
        case OperEx(TlaActionOper.prime, e) =>
          transform(true)(e)

        case OperEx(oper, args @ _*) =>
          OperEx(oper, args map transform(primeToAdd): _*)

        // TODO: ENABLED and module instances need a special treatment

        case nameEx @ NameEx(name) =>
          if (primeToAdd && stateVars.contains(name)) {
            // add prime to a variable name
            OperEx(TlaActionOper.prime, nameEx)
          } else {
            nameEx
          }

        case ex @ LetInEx(body, defs @ _*) =>
          val newDefs = defs.map(tracker.trackOperDecl { x =>
            x.copy(body = transform(primeToAdd)(x.body))
          })
          val newBody = transform(primeToAdd)(body)
          if (defs == newDefs && body == newBody) ex
          else LetInEx(newBody, newDefs: _*)

        case e => e
      }

    transform(primeToAdd = false)(expr)
  }

}
