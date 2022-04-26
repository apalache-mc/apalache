package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed

package object transformations {

  /**
   * Transformation of expressions.
   */
  type TlaExTransformation = TlaEx => TlaEx

  /**
   * A convenient alias to indicate that `Left(ex)` carries an unchanged expression, whereas `Right(ex)` carries a
   * transformed expression.
   */
  type KeepOrTouchEx = Either[TlaEx, TlaEx]

  /**
   * Wrap an expression to indicate that it has not changed.
   *
   * @param ex
   *   TLA+ expression
   * @return
   *   Left(ex)
   */
  def keep(ex: TlaEx): KeepOrTouchEx = Left(ex)

  /**
   * Wrap an expression to indicate that it has changed.
   *
   * @param ex
   *   TLA+ expression
   * @return
   *   Right(ex)
   */
  def touch(ex: TlaEx): KeepOrTouchEx = Right(ex)

  /**
   * An expression transformation that carries a bit of information about the source expression has been transformed or
   * not. By convention, a transformation should return `Left(ex)`, if the expression has not changed, and it should
   * return `Right(ex)`, if the expression has changed. Conveniently, `Left(ex).map(f)` will produce `Left(ex)`, whereas
   * `Right(ex).map(f)` will apply `f` to `ex`.
   */
  type TlaExTouchTransformation = KeepOrTouchEx => KeepOrTouchEx

  /**
   * Transformation of declarations: constants, variables, operators, etc.
   */
  type TlaDeclTransformation = TlaDecl => TlaDecl

  /**
   * This adapter method takes an expression transformation and turns it into a declaration transformation that:
   *   1. Copies the declaration body and applies the expression transformation to it, and 2. Tracks the update of the
   *      declaration
   *
   * @param tracker
   *   transformation tracker
   * @param transformation
   *   expression transformation
   * @return
   *   a declaration transformation that is tracking updates to declarations and expressions inside them.
   */
  def fromExToDeclTransformation(
      tracker: TransformationTracker,
      transformation: TlaExTransformation): TlaDeclTransformation = tracker.trackDecl {
    case d @ TlaOperDecl(_, _, b) =>
      d.copy(body = transformation(b))

    case d => d
  }

  /**
   * This adapter downgrades (the more precise) TlaExTouchTransformation to TlaExTransformation, which forgets about
   * whether the expression has been changed or not.
   *
   * @param transformation
   *   a touch transformation
   * @return
   *   equivalent transformation that drops the change flag
   */
  def fromTouchToExTransformation(transformation: TlaExTouchTransformation): TlaExTransformation = { ex =>
    transformation(touch(ex)).fold(e1 => e1, e2 => e2)
  }

  /**
   * A transformation that makes a module out of a module.
   */
  type TlaModuleTransformation = TlaModule => TlaModule

  /**
   * Returns a transformation which primes all unprimed variables from `vars` appearing in a given expression.
   *
   * Example:
   *
   * {{{
   * a' + b > 0 --> a' + b' > 0
   * }}}
   *
   * @param vars
   *   variables that should be primed
   * @param tracker
   *   a transformation tracker for recording which expressions have changed
   * @return
   *   the transformation that adds primes to the variables from `vars`
   */
  def decorateWithPrime(vars: Set[String], tracker: TransformationTracker): TlaExTransformation = {
    ReplaceFixed(tracker).withFun {
      case ex @ NameEx(name) if vars.contains(name) =>
        // add prime to a variable from vars
        OperEx(TlaActionOper.prime, ex)(ex.typeTag)

      case OperEx(TlaActionOper.prime, primedOnce @ OperEx(TlaActionOper.prime, _)) =>
        // in case the variable was already primed, remove the second prime
        primedOnce
    }
  }
}
