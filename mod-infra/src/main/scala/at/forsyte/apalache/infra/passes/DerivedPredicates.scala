package at.forsyte.apalache.infra.passes

// TODO doc
//
// Allows communicating mutable spec behavior between passes
// TODO What's the right name for this class?
class DerivedPredicates(
    var invariants: List[String],
    var temporal: List[String],
    var next: String,
    var init: String,
    var cinit: String)

object DerivedPredicates {
  def apply(
      invariants: List[String] = List.empty,
      temporal: List[String] = List.empty,
      next: String = "",
      init: String = "",
      cinit: String = ""): DerivedPredicates =
    new DerivedPredicates(invariants: List[String], temporal: List[String], next: String, init: String, cinit: String)
}
