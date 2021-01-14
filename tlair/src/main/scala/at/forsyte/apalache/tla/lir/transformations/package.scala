package at.forsyte.apalache.tla.lir

package object transformations {

  /**
    * Transformation of expressions.
    */
  type TlaExTransformation = TlaEx => TlaEx

  /**
    * Transformation of declarations: constants, variables, operators, etc.
    */
  type TlaDeclTransformation = TlaDecl => TlaDecl

  /**
    * This adapter method takes an expression transformation and turns it into a declaration transformation that:
    * 1. Copies the declaration body and applies the expression transformation to it, and
    * 2. Tracks the update of the declaration
    * @param tracker transformation tracker
    * @param transformation expression transformation
    * @return a declaration transformation that is tracking updates to declarations and expressions inside them.
    */
  def fromExToDeclTransformation(
      tracker: TransformationTracker,
      transformation: TlaExTransformation
  ): TlaDeclTransformation = tracker.trackDecl {
    case d @ TlaOperDecl(_, _, b) =>
      val copy = d.copy(body = transformation(b))
      // see issue #345
      copy.isRecursive = d.isRecursive
      copy

    case d => d
  }

  /**
    * A transformation that makes a module out of a module.
    */
  type TlaModuleTransformation = TlaModule => TlaModule
}
