package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeLiteralAndNameBuilder
import scalaz.Scalaz._
import scalaz._

/**
 * Type-safe builder for names and literals (IR tree leaves)
 *
 * @author
 *   Jure Kukovec
 */
trait LiteralAndNameBuilder extends UnsafeLiteralAndNameBuilder {

  /** i: Int */
  def int(i: BigInt): TBuilderInstruction = _int(i).point[TBuilderInternalState]

  /** s: Str */
  def str(s: String): TBuilderInstruction = _str(s).point[TBuilderInternalState]

  /** b: Bool */
  def bool(b: Boolean): TBuilderInstruction = _bool(b).point[TBuilderInternalState]

  /** BOOLEAN */
  def booleanSet(): TBuilderInstruction = _booleanSet().point[TBuilderInternalState]

  /** STRING */
  def stringSet(): TBuilderInstruction = _stringSet().point[TBuilderInternalState]

  /** Int */
  def intSet(): TBuilderInstruction = _intSet().point[TBuilderInternalState]

  /** Nat */
  def natSet(): TBuilderInstruction = _natSet().point[TBuilderInternalState]

  /** exprName: exType */
  def name(exprName: String, exType: TlaType1): TBuilderInstruction = State[TBuilderContext, TlaEx] { mi =>
    val scope = mi.nameScope

    // If already in scope, type must be the same
    scope.get(exprName).foreach { tt =>
      if (tt != exType)
        throw new TBuilderScopeException(
            s"Name $exprName with type $exType constructed in scope where expected type is $tt."
        )
    }

    val ret = _name(exprName, exType)
    (mi.copy(scope + (exprName -> exType)), ret)
  }

  /** Attempt to infer the type from the scope. Fails if exprName is not in scope. */
  def nameWithInferredType(exprName: String): TBuilderInstruction = get[TBuilderContext].map { mi: TBuilderContext =>
    val scope = mi.nameScope

    val tt = scope.getOrElse(exprName,
        throw new TBuilderScopeException(
            s"Cannot build $exprName: the type of $exprName is not in scope. Use name(exprName, exType) instead."
        ))
    _name(exprName, tt)
  }

}
