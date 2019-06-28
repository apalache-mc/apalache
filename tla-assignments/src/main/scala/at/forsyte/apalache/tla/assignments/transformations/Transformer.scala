package at.forsyte.apalache.tla.assignments.transformations

import at.forsyte.apalache.tla.lir.db.BodyDB
import at.forsyte.apalache.tla.lir.transformations.{TransformationComposition, TransformationListener}

sealed case class Transformer( operBodies : BodyDB )( listeners : TransformationListener* )
  extends TransformationComposition(
    InlineFactory( operBodies, listeners : _* ).InlineAll,
    LetInExplicitFactory( listeners : _* ).AllLetInExplicit,
    EqualityAsContainmentFactory( listeners : _* ).AllEqualityAsContainment,
    UnchengedExplicitFactory( listeners : _* ).AllUnchangedExplicit
  )
