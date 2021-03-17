package at.forsyte.apalache.tla.typecheck.integration

import at.forsyte.apalache.tla.lir.transformations.TransformationListener
import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx, Typed, Untyped}
import at.forsyte.apalache.tla.typecheck.{TlaType1, TypingException}

/**
 * A transformation tracker that throws an exception, if a typed expression has been transformed into an untyped one.
 *
 * @author Igor Konnov
 */
class TypeWatchdogTransformationListener extends TransformationListener {
  override def onTransformation(originalEx: TlaEx, newEx: TlaEx): Unit = {
    (originalEx.typeTag, newEx.typeTag) match {
      case (Typed(_: TlaType1), Untyped()) =>
        throw new TypingException(
            s"A typed expression ${originalEx.ID} was transformed to an untyped expression ${newEx.ID}")

      case _ => ()
    }
  }

  override def onDeclTransformation(originalDecl: TlaDecl, newDecl: TlaDecl): Unit = {
    (originalDecl.typeTag, newDecl.typeTag) match {
      case (Typed(_: TlaType1), Untyped()) =>
        throw new TypingException(
            s"A typed declaration ${originalDecl.name} was transformed to an untyped expression ${newDecl.name}")

      case _ => ()
    }
  }
}
