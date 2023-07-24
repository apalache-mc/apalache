package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext

/**
 * A [[DelayedConstraintGenerator]] may, on demand, discharge SMT constraints.
 *
 * The primary use-case for this trait lies with [[caches.Cache]]s. Instead of instantly discharging SMT constants as
 * soon as an entry is added to the cache, which effectively makes all caches stateful and inextricably liked to
 * [[at.forsyte.apalache.tla.bmcmt.smt.SolverContext]], we can manipulate caches first, then discharge a batch of
 * constraints separately.
 *
 * @tparam ElemT
 *   the type of the contents of the collection extending this trait.
 * @author
 *   Jure Kukovec
 */
trait DelayedConstraintGenerator[ElemT] {

  /** Return a function to add implementation-specific constraints for a single entry */
  def addConstraintsForElem(ctx: SolverContext): ElemT => Unit

  /** Add implementation-specific constraints for all entries. */
  def addAllConstraints(ctx: SolverContext): Unit

}
