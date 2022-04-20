package at.forsyte.apalache.tla.typecmp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecmp._
import at.forsyte.apalache.tla.typecmp.raw.RawLeafBuilder
import scalaz.Scalaz._
import scalaz._

/**
 * Builder for leaf expressions (names and literals)
 *
 * @author
 *   Jure Kukovec
 */
trait LeafBuilder extends RawLeafBuilder {

  def int(i: BigInt): ValWrapper = _int(i).point[InternalState]

  def str(s: String): ValWrapper = _str(s).point[InternalState]

  def bool(b: Boolean): ValWrapper = _bool(b).point[InternalState]

  def booleanSet(): ValWrapper = _booleanSet().point[InternalState]

  def stringSet(): ValWrapper = _stringSet().point[InternalState]

  def intSet(): ValWrapper = _intSet().point[InternalState]

  def natSet(): ValWrapper = _natSet().point[InternalState]

  def name(exprName: String, exType: TlaType1): NameWrapper = State[MetaInfo, NameEx] { mi =>
    val scope = mi.nameScope

    // If already in scope, type must be the same
    scope.get(exprName).foreach { tt =>
      if (tt != exType)
        throw new BuilderScopeException(
            s"Name $exprName with type $exType constructed in scope where expected type is $tt."
        )
    }

    val ret = _name(exprName, exType)
    (mi.copy(scope + (exprName -> exType)), ret)
  }

  // Attempt to get the type from the scope. Fails if not in scope.
  def name(exprName: String): NameWrapper = get[MetaInfo].map { mi: MetaInfo =>
    val scope = mi.nameScope

    val tt = scope.getOrElse(exprName,
        throw new BuilderScopeException(
            s"Cannot build $exprName: the type of $exprName is not in scope. Use name(exprName, exType) instead."
        ))
    _name(exprName, tt)
  }

}
