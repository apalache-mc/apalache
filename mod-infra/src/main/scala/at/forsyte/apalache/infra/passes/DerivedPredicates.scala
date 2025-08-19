package at.forsyte.apalache.infra.passes

import com.google.inject.Inject

/**
 * For shared-memory communication of information about specification predicates between `Pass`es
 *
 * ==Motivation==
 *
 * When checking a spec, there is a set of predicates which are singled out for special treatment, such the predicate
 * which initializes state variables and the predicate that computes state transitions. We call these "specification
 * predicates".
 *
 * A few specification predicates are determined purely on the basis of configuration input. However, most specification
 * predicates can only be finalized after inspecting the given `TlaModule` through a sequence of several passes. We call
 * specification predicates that cannot be determined based on configuration input alone "derived predicates". We can
 * also view specification predicates which ''can'' be derived directly from configuration input as derived predicates
 * which, however, are derived via a constant function that ignores any additional input from the `TlaModule`.
 *
 * Due to the way we are currently sequencing the execution of passes, the only way to communicate data between passes
 * is either to add it on to the `TlaModule` they process, or share some mutable state. Since we aim to keep the
 * `TlaModule` as trim as possible, we opt for the latter (tho see https://github.com/apalache-mc/apalache/issues/2105
 * for a possible alternative). Since derived predicates must be communicated between passes, we need some mutable state
 * to serve as the communication channel. That is the purpose of the `DerivedPredicates` trait.
 *
 * Since most specification predicates are derived predicates, and in order to reduce sources of possible confusion when
 * reasoning about the communication of specification predicates, the communication of all predicates between passes
 * should be via implementations of `DerivedPredicates`.
 *
 * ==Usage==
 *
 * ===Writable access to derived predicates===
 *
 * Passes that need to update the derived predicates should take a [[DerivedPredicates.Configurable]] parameter.
 *
 * {{{
 * import com.google.inject.Inject
 * import at.forsyte.apalache.tla.lir.TlaModule
 * import at.forsyte.apalache.infra.passes.Pass.PassResult
 *
 * class MyPass @Inject() (derivedPreds: DerivedPredicates.Configurable) {
 *
 *   def execute(module: TlaModule): PassResult = {
 *      // compute specification predicates
 *      derivedPreds.configure(
 *        init = init,
 *        next = next,
 *        //  etc...
 *      )
 *   }
 * }
 * }}}
 *
 * Any subsequent passes that receive an injected `DerivedPredicates` will then have access to these predicates names.
 *
 * ===Read only access to derived predicates===
 *
 * Passes that only need to read derived predicates should take a [[DerivedPredicates]] parameter.
 *
 * {{{
 * import com.google.inject.Inject
 * import at.forsyte.apalache.tla.lir.TlaModule
 * import at.forsyte.apalache.infra.passes.Pass.PassResult
 *
 * class MyPass @Inject() (derivedPreds: DerivedPredicates) {
 *
 *   def execute(module: TlaModule): PassResult = {
 *      val init = derivedPreds.init
 *      val next = derivedPreds.next
 *      // etc.
 *   }
 * }
 * }}}
 */
trait DerivedPredicates {

  /** The name of the predicate that will initialize constant values */
  def cinit: Option[String]

  /** The name of the predicate that will initialize state variables (optional) */
  def init: String

  /** A list of names of predicates that specify invariants  (may be empty) */
  def invariants: List[String]

  /** The name of the predicate used to compute state transitions */
  def next: String

  /** A list of names of predicates that specify temporal properties (may be empty) */
  def temporalProps: List[String]

  /** The name of an operator that produces a state view (works with max-error)  (optional) */
  def view: Option[String]

  /** The names of any operators added programmatically, that should not be removed after inlining (may be empty) */
  def persistent: List[String]

  /**
   * List all operator names for the derived predicates
   */
  def operatorNames(): List[String] = {
    init ::
      next ::
      cinit.toList ++
      view.toList ++
      invariants ++
      temporalProps ++
      persistent
  }
}

object DerivedPredicates {

  /**
   * A writeable extension of [[DerivedPredicates]], into which specification predicate names can be written
   *
   * Instances of this trait are used to "send" the derived specification predicates to later passes.
   */
  trait Configurable extends DerivedPredicates {

    /**
     * Set all specification predicates
     *
     * This method aims to ensure that during the configuration of the derived predicates every required predicate value
     * is set. If we allowed direct write access to the individual attributes, we might forget to overwrite a default
     * value during predicate derivation.
     */
    def configure(
        init: String,
        next: String,
        cinit: Option[String],
        view: Option[String],
        invariants: List[String],
        temporalProps: List[String],
        persistent: List[String]): Unit

    /** The optional cinit predicate currently requires possible override at a later stage of derivation */
    def setCinit(cinit: String): Unit

    /** The invariant predicates are extended in subsequent passes */
    def addInvariants(invs: List[String]): Unit

    /** The persistent operators are extended in subsequent passes */
    def addPersistent(names: String*): Unit
  }

  /**
   * The implementation of configurable derived predicates
   *
   * In the intended use case, this class should only be initialized once per pass execution.
   */
  class Impl @Inject() extends DerivedPredicates.Configurable {
    var invariants: List[String] = List.empty
    var temporalProps: List[String] = List.empty
    var next: String = ""
    var init: String = ""
    var cinit: Option[String] = None
    var view: Option[String] = None
    var persistent: List[String] = List.empty

    def configure(
        init: String,
        next: String,
        cinit: Option[String],
        view: Option[String],
        invariants: List[String],
        temporalProps: List[String],
        persistent: List[String]): Unit = {
      this.init = init
      this.next = next
      this.invariants = invariants
      this.temporalProps = temporalProps
      this.view = view
      this.cinit = cinit
      this.persistent = persistent
    }

    def setCinit(cinit: String): Unit = this.cinit = Some(cinit)

    def addInvariants(invs: List[String]): Unit = this.invariants = this.invariants ++ invs

    def addPersistent(names: String*): Unit = this.persistent ++= names
  }

  object Impl {
    def apply(): Impl = new Impl()
  }
}
