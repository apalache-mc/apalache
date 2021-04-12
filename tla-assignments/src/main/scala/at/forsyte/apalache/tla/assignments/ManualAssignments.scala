package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaActionOper, TlaOper}
import at.forsyte.apalache.tla.lir._

/**
 * Instead of relying on the automatic inference of assignment sites, users may instead choose to
 * manually annotate where they expect assignments in their specifications (with BmcOper.assign)
 *
 * This changes automatic assignment detection in the following way:
 * If, for a given (primed) variable `v`, there exists at least one manual assignment
 * [ v' := ... ], then all expressions of the form [ v' = ... ] are ignored as assignment candidates
 * Manual assignments are still required to satisfy both the acyclicity and the covering properties,
 * or assignment finding will fail.
 *
 * Any variable, for which no manual assignemt exists, is handled in the standard way.
 *
 * @author Jure Kukovec
 */
object ManualAssignments {
  type varnameT = String

  /**
   * List all variables with at least one manual assignment site
   */
  def findAll(ex: TlaEx): Set[varnameT] = ex match {
    case OperEx(ApalacheOper.assign, OperEx(TlaActionOper.prime, NameEx(n)), _) =>
      Set(n)
    case OperEx(_, args @ _*) =>
      args.map(findAll).foldLeft(Set.empty[varnameT]) {
        _ ++ _
      }
    case LetInEx(body, defs @ _*) =>
      defs.map(d => findAll(d.body)).foldLeft(findAll(body)) {
        _ ++ _
      }
    case _ => Set.empty
  }
}
