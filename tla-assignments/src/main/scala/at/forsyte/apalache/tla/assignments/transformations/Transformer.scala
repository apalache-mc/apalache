package at.forsyte.apalache.tla.assignments.transformations

import at.forsyte.apalache.tla.lir.db.BodyDB
import at.forsyte.apalache.tla.lir.transformations.TransformationListener
import at.forsyte.apalache.tla.lir.transformations.impl.TransformationComposition

sealed case class Transformer( operBodies : BodyDB )( listeners : TransformationListener* )
  // TODO: Igor @ 01.07.2019: check Function.chain ;-)
  extends TransformationComposition(
    Inline( operBodies, listeners : _* ).InlineAll,
    LetInExplicit( listeners : _* ).AllLetInExplicit,
    EqualityAsContainment( listeners : _* ).AllEqualityAsContainment,
    UnchengedExplicitTracker( listeners : _* ).AllUnchangedExplicit
  )
