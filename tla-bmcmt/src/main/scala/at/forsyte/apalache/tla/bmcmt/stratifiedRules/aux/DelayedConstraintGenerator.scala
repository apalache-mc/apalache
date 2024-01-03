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
 * TODO: See #2668 - Explain when exactly constraints get discharged, and which class is expected to call
 * `addAllConstraints`. Constraints shouldn't be discharged by rewriting rules, but by some transition-manager related
 * class, which ensures every call to push() or checkSat() is preceded by addAllConstraints().
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
