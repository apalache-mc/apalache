package at.forsyte.apalache.infra.passes

// TODO doc
//
// Allows communicating mutable spec behavior between passes
// TODO What's the right name for this class?
trait DerivedPredicates {
  var invariants: List[String]
  var temporal: List[String]
  var next: String
  var init: String
  var cinit: Option[String]
}

object DerivedPredicates {
  class Impl(
      var invariants: List[String],
      var temporal: List[String],
      var next: String,
      var init: String,
      var cinit: Option[String])
      extends DerivedPredicates

  def apply(
      invariants: List[String] = List.empty,
      temporal: List[String] = List.empty,
      next: String = "",
      init: String = "",
      cinit: Option[String] = None): DerivedPredicates =
    new Impl(invariants = invariants, temporal = temporal, next = next, init = init, cinit = cinit)
}
