package at.forsyte.apalache.infra.passes

import com.google.inject.Inject

// TODO doc
//
// Allows communicating mutable spec behavior between passes
//  What's the right name for this class?
trait DerivedPredicates {
  def cinit: Option[String]
  def init: String
  def invariants: List[String]
  def next: String
  def temporal: List[String]
  def view: Option[String]
}

object DerivedPredicates {

  trait Configurable extends DerivedPredicates {
    // TODO: allows reasoning to ensure that all properties are set, and nothing is left out
    def configure(
        init: String,
        next: String,
        cinit: Option[String],
        view: Option[String],
        invariants: List[String],
        temporal: List[String]): Unit

    def setCinit(cinit: String): Unit
    def addInvariants(invs: List[String]): Unit
  }

  class Impl @Inject() extends DerivedPredicates.Configurable {
    var invariants: List[String] = List.empty
    var temporal: List[String] = List.empty
    var next: String = ""
    var init: String = ""
    var cinit: Option[String] = None
    var view: Option[String] = None

    def configure(
        init: String,
        next: String,
        cinit: Option[String],
        view: Option[String],
        invariants: List[String],
        temporal: List[String]): Unit = {
      this.init = init
      this.next = next
      this.invariants = invariants
      this.temporal = temporal
      this.view = view
      this.cinit = cinit
    }

    def setCinit(cinit: String): Unit = this.cinit = Some(cinit)

    def addInvariants(invs: List[String]): Unit = this.invariants ++ invs
  }

  object Impl {
    def apply(): Impl = new Impl()
  }
}
