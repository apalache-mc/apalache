package at.forsyte.apalache.tla.assignments.transformations

import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations.impl.{RecursiveTransformationImpl, TransformationImpl, TransformationTrackerImpl}
import at.forsyte.apalache.tla.lir.transformations.{ExprTransformer, TransformationListener}

sealed case class EqualityAsContainment(listeners : TransformationListener* )
  extends TransformationTrackerImpl( listeners : _* ) { // SIN 1
  val OneEqualityAsContainment: ExprTransformer = track {
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
  val AllEqualityAsContainment: TransformationImpl =
    new RecursiveTransformationImpl( OneEqualityAsContainment )
}
