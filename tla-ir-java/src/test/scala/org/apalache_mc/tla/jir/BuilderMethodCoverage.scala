package org.apalache_mc.tla.jir

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.ScopeUnsafeBuilder

import java.lang.reflect.{Array => ReflectArray, InvocationTargetException, Method}
import java.math.BigInteger
import scala.util.control.NonFatal

/** Invokes every public builder overload and validates its representative success or documented failure path. */
private[jir] object BuilderMethodCoverage {

  /** Exercises every public overload of the checked facade. */
  def exercise(builder: TlaCheckedBuilder): Unit = exerciseBuilder(builder)

  /** Exercises every public overload of the scope-unsafe facade. */
  def exercise(builder: TlaTypedScopeUncheckedBuilder): Unit = exerciseBuilder(builder)

  /** Invokes and validates every facade method exposed by a builder instance. */
  private def exerciseBuilder(builder: AnyRef): Unit = {
    val fixtures = new Fixtures(builder)
    publicMethods(builder).foreach(method => invokeRepresentative(builder, method, fixtures))
  }

  /** Invokes one method and materializes checked results so deferred validation also runs. */
  private def invokeRepresentative(builder: AnyRef, method: Method, fixtures: Fixtures): Unit = {
    try {
      val result = method.invoke(builder, representativeArguments(method, fixtures): _*)
      if (result == null) throw new AssertionError(s"${methodId(method)} returned null")
      materialize(builder, method, result)
    } catch {
      case error: InvocationTargetException => throw failure(method, error.getCause)
      case error: AssertionError            => throw error
      case NonFatal(error)                  => throw failure(method, error)
    }
  }

  /** Supplies a valid representative argument list for one exact facade overload. */
  private def representativeArguments(method: Method, f: Fixtures): Array[AnyRef] = {
    val name = method.getName
    val parameterTypes = method.getParameterTypes
    val count = parameterTypes.length

    (name, count) match {
      case ("build", 1) if parameterTypes.head == classOf[TlaBuilderExpr] => Array(f.expression(f.integer))
      case ("build", 1) if parameterTypes.head == classOf[TlaBuilderDecl] => Array(f.declaration(f.operDecl))
      case ("unchecked", 1)                                               => Array(f.integer)
      case ("uncheckedDecl", 1)                                           => Array(f.operDecl)
      case ("integer", 1) if parameterTypes.head == classOf[BigInteger]   => Array(BigInteger.ONE)
      case ("integer", 1) if parameterTypes.head == java.lang.Long.TYPE   => Array(Long.box(1L))
      case ("str", 1)                                                     => Array("value")
      case ("bool", 1)                                                    => Array(Boolean.box(true))
      case ("constant", 2)                                                => Array("value", f.constantType)
      case ("constParsed", 1)                                             => Array("1_OF_A")
      case ("booleanSet" | "stringSet" | "intSet" | "natSet", 0)          => Array.empty
      case ("name", 2)                                                    => Array("value", IntT1)
      case ("nameWithInferredType", 1)                                    => Array("missing")
      case ("param", 2)                                                   => Array("parameter", IntT1)
      case ("decl", 3)                                                    =>
        Array("Declared", f.parameterBody, f.typedParameters)
      case ("declWithInferredParameterTypes", 3) =>
        Array("Inferred", f.parameterBody, f.operParameters)
      case ("lambda", 3) =>
        Array("Lambda", f.parameterBody, f.typedParameters)
      case ("letIn", 2)           => Array(f.expression(f.integer), f.declarations)
      case ("exceptMany", 2)      => Array(f.expression(f.function), f.updates)
      case ("varDeclAsNameEx", 1) => Array(f.varDecl)
      case ("primeEq", 2)         => Array(f.expression(f.intName), f.expression(f.integer))
      case ("eql" | "neql", 2)    => Array(f.expression(f.integer), f.expression(f.integerTwo))
      case ("operApply", 2)       => Array(f.expression(f.unaryOperator), f.expressions(f.integer))
      case ("choose", 2)          => Array(f.expression(f.boundName), f.expression(f.predicate))
      case ("choose", 3)          =>
        Array(f.expression(f.boundName), f.expression(f.integerSet), f.expression(f.predicate))
      case ("label", 2)             => Array(f.expression(f.predicate), Array("label"))
      case ("and" | "or", 1)        => f.only(f.expressions(f.predicate, f.predicateTwo))
      case ("not", 1)               => Array(f.expression(f.predicate))
      case ("implies" | "equiv", 2) =>
        Array(f.expression(f.predicate), f.expression(f.predicateTwo))
      case ("forall" | "exists", 2) =>
        Array(f.expression(f.boundName), f.expression(f.predicate))
      case ("forall" | "exists", 3) =>
        Array(f.expression(f.boundName), f.expression(f.integerSet), f.expression(f.predicate))
      case ("plus" | "minus" | "mult" | "div" | "mod" | "exp" | "interval" | "lt" | "gt" | "le" | "ge", 2) =>
        Array(f.expression(f.integer), f.expression(f.integerTwo))
      case ("uminus", 1)       => Array(f.expression(f.integer))
      case ("enumSet", 1)      => f.only(f.expressions(f.integer, f.integerTwo))
      case ("emptySet", 1)     => Array(IntT1)
      case ("in" | "notIn", 2) =>
        Array(f.expression(f.integer), f.expression(f.integerSet))
      case ("intersect" | "union" | "subsetEq" | "difference", 2) =>
        Array(f.expression(f.integerSet), f.expression(f.integerSetTwo))
      case ("unionAll", 1) => Array(f.expression(f.nestedIntegerSet))
      case ("filter", 3)   =>
        Array(f.expression(f.boundName), f.expression(f.integerSet), f.expression(f.predicate))
      case ("map", 2)    => Array(f.expression(f.boundName), f.expressionPairs(f.boundName, f.integerSet))
      case ("funSet", 2) =>
        Array(f.expression(f.integerSet), f.expression(f.integerSetTwo))
      case ("recordSet", 1)                   => f.only(f.namedExpressions("field", f.integerSet))
      case ("seqSet", 1)                      => Array(f.expression(f.integerSet))
      case ("times", 1)                       => f.only(f.expressions(f.integerSet, f.integerSetTwo))
      case ("powerSet", 1)                    => Array(f.expression(f.integerSet))
      case ("isFiniteSet" | "cardinality", 1) => Array(f.expression(f.integerSet))
      case ("record", 1)                      => f.only(f.namedExpressions("field", f.integer))
      case ("tuple", 1)                       => f.only(f.expressions(f.integer, f.predicate))
      case ("emptySeq", 1)                    => Array(IntT1)
      case ("seq", 1)                         => f.only(f.expressions(f.integer, f.integerTwo))
      case ("funDef", 2)   => Array(f.expression(f.boundName), f.expressionPairs(f.boundName, f.integerSet))
      case ("funApply", 2) => Array(f.expression(f.function), f.expression(f.integer))
      case ("domain", 1)   => Array(f.expression(f.function))
      case ("except", 3)   =>
        Array(f.expression(f.function), f.expression(f.integer), f.expression(f.integerTwo))
      case ("append", 2) => Array(f.expression(f.integerSequence), f.expression(f.integer))
      case ("concat", 2) =>
        Array(f.expression(f.integerSequence), f.expression(f.integerSequenceTwo))
      case ("head" | "tail" | "len", 1) => Array(f.expression(f.integerSequence))
      case ("subSeq", 3)                =>
        Array(f.expression(f.integerSequence), f.expression(f.integer), f.expression(f.integerTwo))
      case ("prime", 1)                 => Array(f.expression(f.intName))
      case ("stutter" | "noStutter", 2) =>
        Array(f.expression(f.predicate), f.expression(f.intName))
      case ("enabled", 1)    => Array(f.expression(f.predicate))
      case ("unchanged", 1)  => Array(f.expression(f.intName))
      case ("actionThen", 2) => Array(f.expression(f.predicate), f.expression(f.predicateTwo))
      case ("ite", 3)        =>
        Array(f.expression(f.predicate), f.expression(f.integer), f.expression(f.integerTwo))
      case ("caseSplit", 1) => f.only(f.expressionPairs(f.predicate, f.integer))
      case ("caseOther", 2) =>
        Array(f.expression(f.integerTwo), f.expressionPairs(f.predicate, f.integer))
      case ("always" | "eventually", 1)  => Array(f.expression(f.predicate))
      case ("leadsTo" | "guarantees", 2) =>
        Array(f.expression(f.predicate), f.expression(f.predicateTwo))
      case ("weakFair" | "strongFair", 2)           => Array(f.expression(f.intName), f.expression(f.predicate))
      case ("temporalExists" | "temporalForAll", 2) =>
        Array(f.expression(f.boundName), f.expression(f.predicate))
      case ("assign", 2) => Array(f.expression(f.primedInteger), f.expression(f.integerTwo))
      case ("gen", 2)    => Array(f.expression(f.integer), IntT1)
      case ("repeat", 3) if parameterTypes(1) == classOf[BigInteger] =>
        Array(f.expression(f.binaryOperator), BigInteger.ONE, f.expression(f.integer))
      case ("repeat", 3) if parameterTypes(1) == java.lang.Long.TYPE =>
        Array(f.expression(f.binaryOperator), Long.box(1L), f.expression(f.integer))
      case ("skolem", 1)                                              => Array(f.expression(f.existential))
      case ("guess", 1)                                               => Array(f.expression(f.integerSet))
      case ("expand", 1)                                              => Array(f.expression(f.powerSet))
      case ("constCard", 1)                                           => Array(f.expression(f.cardinalityLowerBound))
      case ("mkSeq", 2) if parameterTypes.head == classOf[BigInteger] =>
        Array(BigInteger.ONE, f.expression(f.unaryOperator))
      case ("mkSeq", 2) if parameterTypes.head == java.lang.Long.TYPE =>
        Array(Long.box(1L), f.expression(f.unaryOperator))
      case ("mkSeqConst", 2) =>
        Array(f.expression(f.integer), f.expression(f.unaryOperator))
      case ("foldSet", 3) =>
        Array(f.expression(f.binaryOperator), f.expression(f.integer), f.expression(f.integerSet))
      case ("foldSeq", 3) =>
        Array(f.expression(f.binaryOperator), f.expression(f.integer), f.expression(f.integerSequence))
      case ("setAsFun", 1)                   => Array(f.expression(f.pairSet))
      case ("notSupportedByModelChecker", 2) => Array("unsupported", IntT1)
      case ("distinct", 1)                   => f.only(f.expressions(f.integer, f.integerTwo))
      case ("apalacheSeqCapacity", 1)        => Array(f.expression(f.integerSequence))
      case ("variant", 3)                    => Array("Some", f.expression(f.integer), f.variantType)
      case ("variantFilter", 2)              => Array("Some", f.expression(f.variantSet))
      case ("variantTag", 1)                 => Array(f.expression(f.variantValue))
      case ("variantGetOrElse", 3)           =>
        Array("Some", f.expression(f.variantValue), f.expression(f.integerTwo))
      case ("variantGetUnsafe", 2) => Array("Some", f.expression(f.variantValue))
      case _                       => throw new AssertionError(s"No representative invocation for ${methodId(method)}")
    }
  }

  /** Builds deferred checked results and verifies the one operation that requires pre-existing scope. */
  private def materialize(builder: AnyRef, method: Method, result: AnyRef): Unit = (builder, result) match {
    case (checked: TlaCheckedBuilder, expression: TlaBuilderExpr) if method.getName == "nameWithInferredType" =>
      try {
        checked.build(expression)
        throw new AssertionError("nameWithInferredType unexpectedly succeeded without a known scope entry")
      } catch {
        case _: TlaBuilderScopeException => ()
      }
    case (checked: TlaCheckedBuilder, expression: TlaBuilderExpr)  => checked.build(expression)
    case (checked: TlaCheckedBuilder, declaration: TlaBuilderDecl) => checked.build(declaration)
    case _                                                         => ()
  }

  /** Returns facade methods while excluding methods inherited from `Object`. */
  private def publicMethods(builder: AnyRef): Seq[Method] =
    builder.getClass.getMethods.toSeq
      .filterNot(_.getDeclaringClass == classOf[Object])
      .sortBy(methodId)

  /** Formats a reflected method as a stable diagnostic identifier. */
  private def methodId(method: Method): String =
    s"${method.getName}(${method.getParameterTypes.map(_.getTypeName).mkString(", ")})"

  /** Wraps an invocation failure with the exact facade overload being exercised. */
  private def failure(method: Method, cause: Throwable): AssertionError = {
    val error = new AssertionError(s"Representative invocation failed for ${methodId(method)}: ${cause.getMessage}")
    error.initCause(cause)
    error
  }

  /** Provides raw IR fixtures and converts them to either facade expression representation. */
  final private class Fixtures(builder: AnyRef) {

    /** Converts raw IR to the expression representation accepted by the target facade. */
    def expression(value: TlaEx): AnyRef = checked match {
      case Some(target) => target.unchecked(value)
      case None         => value
    }

    /** Converts raw declarations to the declaration representation accepted by the target facade. */
    def declaration(value: TlaOperDecl): AnyRef = checked match {
      case Some(target) => target.uncheckedDecl(value)
      case None         => value
    }

    /** Creates an expression array with the component type required by the target facade. */
    def expressions(values: TlaEx*): AnyRef = referenceArray(expressionClass, values.map(expression))

    /** Creates a declaration array with the component type required by the target facade. */
    def declarations: AnyRef = referenceArray(declarationClass, Seq(declaration(operDecl)))

    /** Creates a Java expression-pair array for the target facade. */
    def expressionPairs(first: TlaEx, second: TlaEx): AnyRef =
      Array(new ExpressionPair[AnyRef](expression(first), expression(second)))

    /** Creates a Java named-expression array for the target facade. */
    def namedExpressions(name: String, value: TlaEx): AnyRef =
      Array(new NamedExpression[AnyRef](name, expression(value)))

    /** Creates a Java EXCEPT-update array for the target facade. */
    def updates: AnyRef = Array(new ExceptUpdate[AnyRef](expression(integer), expression(integerTwo)))

    /** Wraps one already-created array as a single reflection argument. */
    def only(array: AnyRef): Array[AnyRef] = Array(array)

    val constantType: ConstT1 = ConstT1("A")
    val variantType: VariantT1 = VariantT1(RowT1("Some" -> IntT1))
    val integer: TlaEx = raw.name("integer", IntT1)
    val integerTwo: TlaEx = raw.name("integerTwo", IntT1)
    val intName: TlaEx = raw.name("variable", IntT1)
    val boundName: TlaEx = raw.name("bound", IntT1)
    val predicate: TlaEx = raw.name("predicate", BoolT1)
    val predicateTwo: TlaEx = raw.name("predicateTwo", BoolT1)
    val integerSet: TlaEx = raw.name("integerSet", SetT1(IntT1))
    val integerSetTwo: TlaEx = raw.name("integerSetTwo", SetT1(IntT1))
    val nestedIntegerSet: TlaEx = raw.name("nestedIntegerSet", SetT1(SetT1(IntT1)))
    val integerSequence: TlaEx = raw.name("integerSequence", SeqT1(IntT1))
    val integerSequenceTwo: TlaEx = raw.name("integerSequenceTwo", SeqT1(IntT1))
    val function: TlaEx = raw.name("function", FunT1(IntT1, IntT1))
    val unaryOperator: TlaEx = raw.name("unaryOperator", OperT1(Seq(IntT1), IntT1))
    val binaryOperator: TlaEx = raw.name("binaryOperator", OperT1(Seq(IntT1, IntT1), IntT1))
    val pairSet: TlaEx = raw.name("pairSet", SetT1(TupT1(IntT1, IntT1)))
    val variantValue: TlaEx = raw.name("variantValue", variantType)
    val variantSet: TlaEx = raw.name("variantSet", SetT1(variantType))
    val primedInteger: TlaEx = raw.prime(intName)
    val existential: TlaEx = raw.exists(boundName, integerSet, predicate)
    val powerSet: TlaEx = raw.powSet(integerSet)
    val cardinalityLowerBound: TlaEx = raw.ge(raw.cardinality(integerSet), integer)
    val varDecl: TlaVarDecl = TlaVarDecl("variable")(Typed(IntT1))
    val operDecl: TlaOperDecl = raw.decl("Fixture", integer)
    val parameterBody: AnyRef = checked match {
      case Some(target) => target.name("parameter", IntT1)
      case None         => raw.name("parameter", IntT1)
    }
    val typedParameters: AnyRef = Array(new TypedParameter("parameter", IntT1))
    val operParameters: AnyRef = Array(OperParam("parameter"))

    private lazy val raw = new ScopeUnsafeBuilder(strict = false)
    private lazy val checked = builder match {
      case target: TlaCheckedBuilder        => Some(target)
      case _: TlaTypedScopeUncheckedBuilder => None
      case other                            =>
        throw new IllegalArgumentException(s"Unsupported facade builder: ${other.getClass.getName}")
    }
    private lazy val expressionClass = checked.fold[Class[_]](classOf[TlaEx])(_ => classOf[TlaBuilderExpr])
    private lazy val declarationClass = checked.fold[Class[_]](classOf[TlaOperDecl])(_ => classOf[TlaBuilderDecl])

    /** Creates a runtime-typed reference array for reflective varargs calls. */
    private def referenceArray(componentType: Class[_], values: Seq[AnyRef]): AnyRef = {
      val array = ReflectArray.newInstance(componentType, values.size)
      values.zipWithIndex.foreach { case (value, index) => ReflectArray.set(array, index, value) }
      array
    }
  }
}
