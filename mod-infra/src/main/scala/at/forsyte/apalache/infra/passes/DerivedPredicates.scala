package at.forsyte.apalache.infra.passes

import com.google.inject.Inject

// TODO doc
//
// Allows communicating mutable spec behavior between passes
//  What's the right name for this class?
trait DerivedPredicates {
  var invariants: List[String]
  var temporal: List[String]
  var next: String
  var init: String
  var cinit: Option[String]
}

object DerivedPredicates {

  class Impl @Inject() extends DerivedPredicates {
    var invariants: List[String] = List.empty
    var temporal: List[String] = List.empty
    var next: String = ""
    var init: String = ""
    var cinit: Option[String] = None
  }

  object Impl {
    def apply(): Impl = new Impl()
  }
}
