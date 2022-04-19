package at.forsyte.apalache.tla.typecmp.subbuilder

import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecmp._
import scalaz.Scalaz._
import scalaz._

/**
 * Builder for leaf expressions (names and literals)
 *
 * @author
 *   Jure Kukovec
 */
trait LeafBuilder {

  def int(i: BigInt): BuilderWrapper = ValEx(TlaInt(i))(Typed(IntT1())).asInstanceOf[TlaEx].point[InternalState]

  def str(s: String): BuilderWrapper = ValEx(TlaStr(s))(Typed(StrT1())).asInstanceOf[TlaEx].point[InternalState]

  def bool(b: Boolean): BuilderWrapper = ValEx(TlaBool(b))(Typed(BoolT1())).asInstanceOf[TlaEx].point[InternalState]

  def booleanSet(): BuilderWrapper = ValEx(TlaBoolSet)(Typed(SetT1(BoolT1()))).asInstanceOf[TlaEx].point[InternalState]

  def stringSet(): BuilderWrapper = ValEx(TlaStrSet)(Typed(SetT1(StrT1()))).asInstanceOf[TlaEx].point[InternalState]

  def intSet(): BuilderWrapper = ValEx(TlaIntSet)(Typed(SetT1(IntT1()))).asInstanceOf[TlaEx].point[InternalState]

  def natSet(): BuilderWrapper = ValEx(TlaNatSet)(Typed(SetT1(IntT1()))).asInstanceOf[TlaEx].point[InternalState]

  def name(exprName: String, exType: TlaType1): BuilderWrapper = State[MetaInfo, builderReturn] { mi =>
    val scope = mi.nameScope

    // If already in scope, type must be the same
    scope.get(exprName).foreach { tt =>
      if (tt != exType)
        throw new BuilderScopeException(
            s"Name $exprName with type $exType constructed in scope where expected type is $tt."
        )
    }

    val ret = NameEx(exprName)(Typed(exType))
    (mi.copy(scope + (exprName -> exType)), ret)
  }

  // Attempt to get the type from the scope. Fails if not in scope.
  def name(exprName: String): BuilderWrapper = get[MetaInfo].map { mi: MetaInfo =>
    val scope = mi.nameScope

    val tt = scope.getOrElse(exprName,
        throw new BuilderScopeException(
            s"Cannot build $exprName: the type of $exprName is not in scope. Use name(exprName, exType) instead."
        ))
    NameEx(exprName)(Typed(tt))
  }

}
