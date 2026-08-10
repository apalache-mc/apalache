package org.apalache_mc.tla.jir

import org.scalatest.funsuite.AnyFunSuite

import java.lang.reflect.{Constructor, Method, Modifier, Type}

/**
 * Verifies properties of the compiled facade API that matter to Java callers.
 *
 * These reflection checks prevent Scala and implementation-only types from leaking through public signatures, keep
 * deferred checked-builder state inaccessible, and ensure repeated arguments remain convenient Java varargs.
 */
class TestPublicApi extends AnyFunSuite {
  test("public methods and constructors do not expose Scala or implementation-only types") {
    facadeApiClasses.foreach { facadeClass =>
      publicFacadeMethods(facadeClass).foreach(assertMethodSignatureUsesJavaTypes)
      facadeClass.getConstructors.foreach(assertConstructorSignatureUsesJavaTypes)
    }
  }

  test("checked-builder expression and declaration handles do not expose their internal state") {
    Seq(classOf[TlaBuilderExpr], classOf[TlaBuilderDecl]).foreach { handleClass =>
      assert(handleClass.getDeclaredMethods.forall(method => !Modifier.isPublic(method.getModifiers)))
      assert(handleClass.getConstructors.isEmpty)
    }
  }

  test("public methods with a trailing array parameter are declared as Java varargs") {
    facadeApiClasses
      .flatMap(publicFacadeMethods)
      .filter(_.getParameterTypes.lastOption.exists(_.isArray))
      .foreach { method =>
        assert(method.isVarArgs, s"${method.getDeclaringClass.getName}.${method.getName} is not a Java varargs method")
      }
  }

  /** Verifies the parameter and return types of one public facade method. */
  private def assertMethodSignatureUsesJavaTypes(method: Method): Unit = {
    // Java value records necessarily declare equals(Object); this standard override is the only intentionally untyped
    // facade signature.
    val isEqualsOverride = method.getName == "equals" && method.getParameterTypes.sameElements(Array(classOf[Object]))
    if (!isEqualsOverride) {
      assertTypesAreJavaFacing(
          method.getDeclaringClass,
          method.getName,
          method.getGenericParameterTypes.toSeq :+ method.getGenericReturnType,
      )
    }
  }

  /** Returns the public methods implemented by the facade rather than methods inherited from the JDK. */
  private def publicFacadeMethods(facadeClass: Class[_]): Seq[Method] =
    facadeClass.getMethods.filter(_.getDeclaringClass.getPackageName == facadePackageName).toSeq

  /** Verifies the parameter types of one public facade constructor. */
  private def assertConstructorSignatureUsesJavaTypes(constructor: Constructor[_]): Unit = {
    assertTypesAreJavaFacing(constructor.getDeclaringClass, "<init>", constructor.getGenericParameterTypes.toSeq)
  }

  /** Rejects API types tied to Scala, facade internals, or an uninformative `Object`. */
  private def assertTypesAreJavaFacing(owner: Class[_], member: String, types: Seq[Type]): Unit = {
    types.foreach { apiType =>
      val typeName = apiType.getTypeName
      implementationTypeNameFragments.foreach { fragment =>
        assert(!typeName.contains(fragment), s"$owner.$member exposes implementation type $typeName")
      }
      assert(typeName != "java.lang.Object", s"$owner.$member exposes untyped Object")
    }
  }

  private val facadePackageName = "org.apalache_mc.tla.jir"

  private val facadeApiClasses = Seq(
      classOf[TlaCheckedBuilder],
      classOf[TlaTypedScopeUncheckedBuilder],
      classOf[TlaBuilderExpr],
      classOf[TlaBuilderDecl],
      classOf[TlaTypes],
      classOf[TlaDeclarations],
      classOf[ExpressionPair[_]],
      classOf[NamedExpression[_]],
      classOf[ExceptUpdate[_]],
      classOf[TypedParameter],
      classOf[NamedType],
      classOf[IndexedType],
      classOf[TlaBuilderException],
      classOf[TlaBuilderTypeException],
      classOf[TlaBuilderScopeException],
  )

  private val implementationTypeNameFragments = Seq("scala.", "scalaz.", "$", "JavaFacadeSupport")
}
