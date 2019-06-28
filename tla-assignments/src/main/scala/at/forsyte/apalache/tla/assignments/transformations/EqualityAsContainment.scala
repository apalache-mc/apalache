package at.forsyte.apalache.tla.assignments.transformations

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.{TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations.{RecursiveTransformation, Transformation, TransformationFactory, TransformationListener}

sealed case class EqualityAsContainmentFactory( listeners : TransformationListener* )
  extends TransformationFactory( listeners : _* ) {
  val OneEqualityAsContainment: Transformation = listenTo {
    case OperEx( TlaOper.eq, lhs@OperEx( TlaActionOper.prime, _ ), rhs ) =>
      OperEx( TlaSetOper.in, lhs, OperEx( TlaSetOper.enumSet, rhs ) )
    case e => e
  }

  /**
    * Recursively replaces prime assignments with set membership.
    *
    * Example:
    * x' = y --> x' \in {y}
    */
  val AllEqualityAsContainment: Transformation =
    new RecursiveTransformation( OneEqualityAsContainment )
}
