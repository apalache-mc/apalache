package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeLiteralAndNameBuilder
import scalaz.Scalaz._
import scalaz._

/**
 * Scope-safe builder for names and literals (IR tree leaves)
 *
 * @author
 *   Jure Kukovec
 */
trait LiteralAndNameBuilder {
  private val unsafeBuilder = new UnsafeLiteralAndNameBuilder

  /** {{{i : Int}}} */
  def int(i: BigInt): TBuilderInstruction = unsafeBuilder.int(i).point[TBuilderInternalState]

  /**
   * {{{s : Str}}}
   * @param s
   *   must be a string literal, not a literal of an uninterpreted sort.
   */
  def str(s: String): TBuilderInstruction = unsafeBuilder.str(s).point[TBuilderInternalState]

  /** {{{b : Bool}}} */
  def bool(b: Boolean): TBuilderInstruction = unsafeBuilder.bool(b).point[TBuilderInternalState]

  /**
   * {{{root_OF_A : A}}}
   * @param root
   *   must be a string identifier and may not contain the `_OF_` suffix.
   */
  def const(root: String, A: ConstT1): TBuilderInstruction = unsafeBuilder.const(root, A).point[TBuilderInternalState]

  /**
   * {{{v : A}}}
   * @param v
   *   must be a literal of an uninterpreted sort, not a string literal.
   */
  def constParsed(v: String): TBuilderInstruction = unsafeBuilder.constParsed(v).point[TBuilderInternalState]

  /** {{{BOOLEAN}}} */
  def booleanSet(): TBuilderInstruction = unsafeBuilder.booleanSet().point[TBuilderInternalState]

  /** {{{STRING}}} */
  def stringSet(): TBuilderInstruction = unsafeBuilder.stringSet().point[TBuilderInternalState]

  /** {{{Int}}} */
  def intSet(): TBuilderInstruction = unsafeBuilder.intSet().point[TBuilderInternalState]

  /** {{{Nat}}} */
  def natSet(): TBuilderInstruction = unsafeBuilder.natSet().point[TBuilderInternalState]

  /** {{{exprName: t}}} */
  def name(exprName: String, t: TlaType1): TBuilderInstruction = State[TBuilderContext, TlaEx] { mi =>
    val scope = mi.freeNameScope

    // If already in scope, type must be the same
    scope.get(exprName).foreach { tt =>
      if (tt != t)
        throw new TBuilderScopeException(
            s"Name $exprName with type $t constructed in scope where expected type is $tt."
        )
    }

    val ret = unsafeBuilder.name(exprName, t)
    (mi.copy(freeNameScope = scope + (exprName -> t), usedNames = mi.usedNames + exprName), ret)
  }

  /** Attempt to infer the type from the scope. Fails if exprName is not in scope. */
  def nameWithInferredType(exprName: String): TBuilderInstruction = get[TBuilderContext].map { mi: TBuilderContext =>
    val scope = mi.freeNameScope

    val tt = scope.getOrElse(exprName,
        throw new TBuilderScopeException(
            s"Cannot build $exprName: the type of $exprName is not in scope. Use name(exprName, exType) instead."
        ))
    unsafeBuilder.name(exprName, tt)
  }

}
