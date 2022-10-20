package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.types.TypeVarPool
import at.forsyte.apalache.tla.types.parser.{DefaultType1Parser, Type1Parser}
import org.easymock.EasyMock
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.easymock.EasyMockSugar
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestEtcTypeChecker extends AnyFunSuite with EasyMockSugar with BeforeAndAfterEach with EtcBuilder {
  private val parser: Type1Parser = DefaultType1Parser
  private var checker: TypeChecker = _

  override protected def beforeEach(): Unit = {
    checker = new EtcTypeChecker(new TypeVarPool(start = 1000))
  }

  // wrap an expression with a let-in definition, as we like to test individual expressions
  private def wrapWithLet(expr: EtcExpr): EtcLet = {
    mkUniqLet("wrapper", mkUniqAbs(expr), mkUniqName("wrapper"))
  }

  // consume the type of the wrapper and auxiliary expressions
  private def consumeWrapperTypes(listener: TypeCheckerListener, wrapper: EtcLet): Unit = {
    for (ex <- Seq(wrapper, wrapper.bound, wrapper.body)) {
      listener.onTypeFound(EasyMock.eq(ex.sourceRef.asInstanceOf[ExactRef]), EasyMock.anyObject[TlaType1]).anyTimes()
    }
    // consume this error, as the interesting error should have been reported before
    listener
      .onTypeError(wrapper.sourceRef.asInstanceOf[ExactRef], "Error when computing the type of wrapper")
      .anyTimes()
  }

  test("check monotypes") {
    val mono = mkUniqConst(parser("Int -> Int"))
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(mono)
    expecting {
      listener.onTypeFound(mono.sourceRef.asInstanceOf[ExactRef], mono.polytype)
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => (Int -> Int)"))) // the expression is wrapped with LET-IN
    }
  }

  test("check names") {
    val expr = mkUniqName("foo")
    val listener = mock[TypeCheckerListener]
    val intSet = parser("Set(Int)")
    val wrapper = wrapWithLet(expr)
    expecting {
      listener.onTypeFound(expr.sourceRef.asInstanceOf[ExactRef], intSet)
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext("foo" -> TlaType1Scheme(intSet, Set.empty)), wrapper)
      assert(computed.contains(parser("() => Set(Int)")))
    }
  }

  test("well-typed application") {
    val oper = parser("Int => Int")
    val arg = mkUniqConst(IntT1)
    val app = mkUniqApp(Seq(oper), arg)
    val listener = mock[TypeCheckerListener]
    val int = IntT1
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(arg.sourceRef.asInstanceOf[ExactRef], int)
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], int)
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => Int")))
    }
  }

  test("well-typed polymorphic application") {
    val oper = parser("a => Seq(a)")
    val arg = mkUniqConst(parser("Set(Int)")) // the argument is parameterized itself
    val app = mkUniqApp(Seq(oper), arg)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(arg.sourceRef.asInstanceOf[ExactRef], parser("Set(Int)"))
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("Seq(Set(Int))"))
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => Seq(Set(Int))")))
    }
  }

  test("ill-typed application") {
    val oper = parser("Int => Int")
    val arg = mkUniqConst(BoolT1)
    val app = mkUniqApp(Seq(oper), arg)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef],
          "An operator with the signature ((Int) => Int) cannot be applied to the provided argument of type Bool")
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.isEmpty)
    }
  }

  test("ill-typed application with custom error explanation") {
    val oper = parser("Int => Int")
    val arg = mkUniqConst(BoolT1)
    val app = mkUniqApp(Seq(oper), arg)
    val listener = mock[TypeCheckerListener]
    app.typeErrorExplanation = (_: List[TlaType1], _: List[TlaType1]) => Some("Mocked explanation")
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef], "Mocked explanation")
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.isEmpty)
    }
  }

  test("unresolved argument") {
    val oper = parser("a => c")
    val arg = mkUniqConst(parser("b"))
    val app = mkUniqApp(Seq(oper), arg)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(arg.sourceRef.asInstanceOf[ExactRef], parser("a"))
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("c"))
      listener.onTypeFound(wrapper.sourceRef.asInstanceOf[ExactRef], parser("() => c"))

      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => c")))
    }
  }

  test("unresolved result") {
    val oper = parser("Int => a")
    val arg = mkUniqConst(IntT1)
    val app = mkUniqApp(Seq(oper), arg)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(arg.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("a"))
      listener.onTypeFound(wrapper.sourceRef.asInstanceOf[ExactRef], parser("() => a"))

      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => a")))
    }
  }

  test("one resolved, one unresolved") {
    val operTypes = Seq(parser("Int => a"), parser("Int => Bool"))
    val arg = mkUniqConst(IntT1)
    val app = mkUniqApp(operTypes, arg)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef],
          "Annotation required. Found 2 matching operator signatures ((Int) => a) or ((Int) => Bool) for argument Int")

      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.isEmpty)
    }
  }

  test("multiple signatures") {
    val operTypes = Seq(parser("Int => Int"), parser("Bool => Bool"))
    val arg = mkUniqConst(IntT1)
    val app = mkUniqApp(operTypes, arg)
    val listener = mock[TypeCheckerListener]
    val int = IntT1
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(arg.sourceRef.asInstanceOf[ExactRef], int)
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], int)
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => Int")))
    }
  }

  test("error: multiple signatures") {
    val operTypes = Seq(parser("a => Int"), parser("a => Bool"))
    val arg = mkUniqConst(IntT1)
    val app = mkUniqApp(operTypes, arg)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef],
          "Annotation required. Found 2 matching operator signatures ((a) => Int) or ((a) => Bool) for argument Int")
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.isEmpty)
    }
  }

  test("error: multiple signatures with custom error explanation") {
    val operTypes = Seq(parser("a => Int"), parser("a => Bool"))
    val arg = mkUniqConst(IntT1)
    val app = mkUniqApp(operTypes, arg)
    app.typeErrorExplanation = (_: List[TlaType1], _: List[TlaType1]) => Some("Mocked explanation")
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef], "Mocked explanation")
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.isEmpty)
    }
  }

  test("well-typed application by name") {
    val arg = mkUniqConst(IntT1)
    val operName = mkUniqName("F")
    val app = mkUniqAppByName(operName, arg)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(operName.sourceRef.asInstanceOf[ExactRef], parser("Int => Int"))
      listener.onTypeFound(arg.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val operType = parser("Int => Int")
      val computed = checker.compute(listener, TypeContext("F" -> TlaType1Scheme(operType, Set.empty)), wrapper)
      assert(computed.contains(parser("() => Int")))
    }
  }

  test("well-typed parameterized application by name") {
    val argInt = mkUniqConst(IntT1)
    val argStr = mkUniqConst(StrT1)
    val operNameInInt = mkUniqName("F")
    val operNameInStr = mkUniqName("F")
    val appInt = mkUniqAppByName(operNameInInt, argInt)
    val appStr = mkUniqAppByName(operNameInStr, argStr)
    val consume = mkUniqApp(Seq(OperT1(Seq(IntT1, StrT1), BoolT1)), appInt, appStr)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(consume)
    expecting {
      listener.onTypeFound(operNameInInt.sourceRef.asInstanceOf[ExactRef], parser("Int => Int")).atLeastOnce()
      listener.onTypeFound(operNameInStr.sourceRef.asInstanceOf[ExactRef], parser("Str => Str")).atLeastOnce()
      listener.onTypeFound(argInt.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      listener.onTypeFound(appInt.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      listener.onTypeFound(argStr.sourceRef.asInstanceOf[ExactRef], parser("Str"))
      listener.onTypeFound(appStr.sourceRef.asInstanceOf[ExactRef], parser("Str"))
      listener.onTypeFound(consume.sourceRef.asInstanceOf[ExactRef], parser("Bool"))
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val operType = parser("a1002 => a1002")
      val computed =
        checker.compute(listener, TypeContext("F" -> TlaType1Scheme(operType, operType.usedNames)), wrapper)
      assert(computed.contains(parser("() => Bool")))
    }
  }

  test("no upward errors on nested error") {
    val arg = mkUniqConst(BoolT1)
    val innerApp = mkUniqApp(Seq(parser("Int => Int")), arg)
    val outerApp = mkUniqApp(Seq(parser("Int => Int")), innerApp)

    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(outerApp)
    expecting {
      listener.onTypeError(innerApp.sourceRef.asInstanceOf[ExactRef],
          "An operator with the signature ((Int) => Int) cannot be applied to the provided argument of type Bool")
      // There is no error about outerApp. Otherwise, we would introduce a long string of errors.
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.isEmpty)
    }
  }

  test("well-typed application of unary lambda") {
    val xDomain = mkUniqConst(parser("Set(Int)"))
    val pred = mkUniqConst(parser("Bool"))
    val xName = mkUniqName("x")
    // lambda x \in Set(Int): Bool
    val lambda = mkUniqAbs(
        pred, // this is a predicate
        (xName, xDomain), // the scope of the variable x, which is used in the predicate
    ) /////
    val operType = parser("(a => Bool) => Set(a)")
    val app = mkUniqApp(Seq(operType), lambda)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(xName.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      listener.onTypeFound(pred.sourceRef.asInstanceOf[ExactRef], parser("Bool")).atLeastOnce()
      listener.onTypeFound(xDomain.sourceRef.asInstanceOf[ExactRef], parser("Set(Int)")).atLeastOnce()
      listener.onTypeFound(lambda.sourceRef.asInstanceOf[ExactRef], parser("Int => Bool")).atLeastOnce()
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("Set(Int)")).atLeastOnce()
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => Set(Int)")))
    }
  }

  test("well-typed application of binary lambda") {
    val xDomain = mkUniqConst(parser("Set(Int)"))
    val yDomain = mkUniqConst(parser("Set(Str)"))
    val pred = mkUniqConst(parser("Bool"))
    val xName = mkUniqName("x")
    val yName = mkUniqName("y")
    // lambda x \in Set(Int), y \in Set(Str): Bool
    val lambda = mkUniqAbs(
        pred, // this is a predicate
        (xName, xDomain), // the scope of the variable x, which is used in the predicate
        (yName, yDomain), // the scope of the variable y, which is used in the predicate
    ) /////
    val operType = parser("((a, b) => Bool) => Set(<<a, b>>)")
    val app = mkUniqApp(Seq(operType), lambda)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(xName.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      listener.onTypeFound(yName.sourceRef.asInstanceOf[ExactRef], parser("Str")).atLeastOnce()
      listener.onTypeFound(pred.sourceRef.asInstanceOf[ExactRef], parser("Bool")).atLeastOnce()
      listener.onTypeFound(xDomain.sourceRef.asInstanceOf[ExactRef], xDomain.polytype).atLeastOnce()
      listener.onTypeFound(yDomain.sourceRef.asInstanceOf[ExactRef], yDomain.polytype).atLeastOnce()
      listener.onTypeFound(lambda.sourceRef.asInstanceOf[ExactRef], parser("(Int, Str) => Bool")).atLeastOnce()
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("Set(<<Int, Str>>)")).atLeastOnce()
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => Set(<<Int, Str>>)")))
    }
  }

  test("ill-typed application of unary lambda") {
    val domain = mkUniqConst(parser("Int"))
    val xName = mkUniqName("x")
    // lambda x \in Int: Bool
    val lambda = mkUniqAbs(
        mkUniqConst(parser("Bool")), // this is a predicate
        (xName, domain), // the ill-typed scope of the variable x
    ) /////
    val operType = parser("(a => Bool) => Set(a)")
    val app = mkUniqApp(Seq(operType), lambda)
    val wrapper = wrapWithLet(app)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeError(domain.sourceRef.asInstanceOf[ExactRef], "Expected a set. Found: Int")
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.isEmpty)
    }
  }

  test("well-typed application of let-in") {
    // let F == lambda x \in Set(Int): x in F(Int)
    val xDomain = mkUniqConst(parser("Set(Int)"))
    val xName = mkUniqName("x")
    val xInF = mkUniqName("x")
    val fBody = mkUniqAbs(xInF, (xName, xDomain))
    val fArg = mkUniqConst(IntT1)
    val fName = mkUniqName("F")
    val fApp = mkUniqAppByName(fName, fArg)
    val letIn = mkUniqLet("F", fBody, fApp)

    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeFound(fName.sourceRef.asInstanceOf[ExactRef], parser("Int => Int"))
      // the variable x has type Int
      listener.onTypeFound(xName.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      // the argument to F has the monotype Int
      listener.onTypeFound(fArg.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      // the result of applying F(Int) is Int
      listener.onTypeFound(fApp.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      // the signature a => a gives us the polymorhic type of x
      listener.onTypeFound(xInF.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      // the signature a => a gives us the polymorphic type of xDomain
      listener.onTypeFound(xDomain.sourceRef.asInstanceOf[ExactRef], parser("Set(Int)")).atLeastOnce()
      // the signature a => a gives us the polymorphic type for the definition of F
      listener.onTypeFound(fBody.sourceRef.asInstanceOf[ExactRef], parser("Int => Int")).atLeastOnce()
      // interestingly, we do not infer the type of F at the application site
//      listener.onTypeFound(fBody.tlaId, parser("Int => Int")).atLeastOnce()
      // the overall result of LET-IN
      listener.onTypeFound(letIn.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
    }
    whenExecuting(listener) {
      // we do not compute principal types here....
      val annotations = TypeContext("F" -> TlaType1Scheme(parser("Int => Int"), Set.empty))
      val computed = checker.compute(listener, annotations, letIn)
      assert(computed.contains(parser("Int")))
    }
  }

  // for monotypes, we can easily infer the types of the definitions
  test("inferring a let-in definition") {
    // let F == lambda x \in Set(Int): x in F(Int)
    val xDomain = mkUniqConst(parser("Set(Int)"))
    val xName = mkUniqName("x")
    val xInF = mkUniqName("x")
    val fBody = mkUniqAbs(xInF, (xName, xDomain))
    val fArg = mkUniqConst(IntT1)
    val fName = mkUniqName("F")
    val fApp = mkUniqAppByName(fName, fArg)
    val letIn = mkUniqLet("F", fBody, fApp)

    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeFound(fName.sourceRef.asInstanceOf[ExactRef], parser("Int => Int"))
      // variable x has the type Int
      listener.onTypeFound(xName.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      // the argument to F has the monotype Int
      listener.onTypeFound(fArg.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      // the result of applying F(Int) is Int
      listener.onTypeFound(fApp.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      // xDomain is Set(Int), it is trivial to infer the type
      listener.onTypeFound(xDomain.sourceRef.asInstanceOf[ExactRef], parser("Set(Int)")).atLeastOnce()
      // we infer x: Int from x \in Set(Int)
      listener.onTypeFound(xInF.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      // in this case, we trivially infer the type of F
      listener.onTypeFound(fBody.sourceRef.asInstanceOf[ExactRef], parser("Int => Int")).atLeastOnce()
      // interestingly, we do not infer the type of F at the application site
//      listener.onTypeFound(fBody.tlaId, parser("Int => Int")).atLeastOnce()
      // the overall result of LET-IN
      listener.onTypeFound(letIn.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, letIn)
      assert(computed.contains(parser("Int")))
    }
  }

  test("polymorphic let-definition") {
    // let F == lambda x \in Set(a): ((c, c) => c) x d in F(Int)
    val xDomain = mkUniqConst(parser("Set(a)"))
    val xNameInApp = mkUniqName("x")
    val d = mkUniqConst(parser("d"))
    val setInF = mkUniqApp(Seq(parser("(c, c) => c")), xNameInApp, d)
    val xName = mkUniqName("x")
    val fBody = mkUniqAbs(setInF, (xName, xDomain))
    val fArg = mkUniqConst(IntT1)
    val fName = mkUniqName("F")
    val fApp = mkUniqAppByName(fName, fArg)
    val letIn = mkUniqLet("F", fBody, fApp)

    val listener = mock[TypeCheckerListener]
    expecting {
      // variable x has a parametric type
      listener.onTypeFound(xName.sourceRef.asInstanceOf[ExactRef], parser("a")).atLeastOnce()
      listener.onTypeFound(xNameInApp.sourceRef.asInstanceOf[ExactRef], parser("a")).atLeastOnce()
      // d has the same type!
      listener.onTypeFound(d.sourceRef.asInstanceOf[ExactRef], parser("a")).atLeastOnce()
      // xDomain is Set(a), the type a propagates
      listener.onTypeFound(xDomain.sourceRef.asInstanceOf[ExactRef], parser("Set(a)")).atLeastOnce()
      listener.onTypeFound(fBody.sourceRef.asInstanceOf[ExactRef], parser("a => a")).atLeastOnce()
      listener.onTypeFound(setInF.sourceRef.asInstanceOf[ExactRef], parser("a"))
      listener.onTypeFound(fApp.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      listener.onTypeFound(fArg.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      listener.onTypeFound(letIn.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      // although the type of F is concrete here, the type of the let-in definition is parametric!
      listener.onTypeFound(fName.sourceRef.asInstanceOf[ExactRef], parser("Int => Int"))
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, letIn)
      assert(computed.contains(parser("Int")))
    }
  }

  test("annotated polymorphic let-definition") {
    // The names of type variables may change during type inference
    // @type: a => a;
    // let F == lambda x \in Set(a): ((c, c) => c) x d in F(Int)
    val xDomain = mkUniqConst(parser("Set(c)"))
    val xNameInApp = mkUniqName("x")
    val d = mkUniqConst(parser("d"))
    val setInF = mkUniqApp(Seq(parser("(c, c) => c")), xNameInApp, d)
    val xName = mkUniqName("x")
    val fBody = mkUniqAbs(setInF, (xName, xDomain))
    val fArg = mkUniqConst(IntT1)
    val fName = mkUniqName("F")
    val fApp = mkUniqAppByName(fName, fArg)
    val letIn = mkUniqLet("F", fBody, fApp)

    val listener = mock[TypeCheckerListener]
    expecting {
      // variable x has a parametric type
      listener.onTypeFound(xName.sourceRef.asInstanceOf[ExactRef], parser("a")).atLeastOnce()
      listener.onTypeFound(xNameInApp.sourceRef.asInstanceOf[ExactRef], parser("a")).atLeastOnce()
      // d has the same type!
      listener.onTypeFound(d.sourceRef.asInstanceOf[ExactRef], parser("a")).atLeastOnce()
      // xDomain is Set(a), the type a propagates
      listener.onTypeFound(xDomain.sourceRef.asInstanceOf[ExactRef], parser("Set(a)")).atLeastOnce()
      listener.onTypeFound(fBody.sourceRef.asInstanceOf[ExactRef], parser("a => a")).atLeastOnce()
      listener.onTypeFound(setInF.sourceRef.asInstanceOf[ExactRef], parser("a"))
      listener.onTypeFound(fApp.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      listener.onTypeFound(fArg.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      listener.onTypeFound(letIn.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      // although the type of F is concrete here, the type of the let-in definition is parametric!
      listener.onTypeFound(fName.sourceRef.asInstanceOf[ExactRef], parser("Int => Int"))
    }
    whenExecuting(listener) {
      // add the type annotation F: \A a: a => a
      val context = TypeContext("F" -> TlaType1Scheme(parser("a => a"), Set(0, 1)))
      val computed = checker.compute(listener, context, letIn)
      assert(computed.contains(parser("Int")))
    }
  }

  test("annotation shall not override the inferred type") {
    // The scenario that was causing a tricky behavior:
    // The inferred type of F uses one set of variables, while the annotated type uses another set.
    // The bug appeared only in the case when using two instances of the constraint solver, so it needed a complex setup.
    //
    // let G ==
    //   @type: a => a;
    //   let F == lambda x \in Set(a): ((c, c) => c) x d
    //   in F(Int)
    // in
    // Bool
    val xDomain = mkUniqConst(parser("Set(c)"))
    val xNameInApp = mkUniqName("x")
    val d = mkUniqConst(parser("d"))
    val setInF = mkUniqApp(Seq(parser("(c, c) => c")), xNameInApp, d)
    val xName = mkUniqName("x")
    val fBody = mkUniqAbs(setInF, (xName, xDomain))
    val fArg = mkUniqConst(IntT1)
    val fName = mkUniqName("F")
    val fApp = mkUniqAppByName(fName, fArg)
    val letInF = mkUniqLet("F", fBody, fApp)
    // add the type annotation F: \A a: a => a
    val annotatedLetInF = mkUniqTypeDecl("F", parser("a => a"), letInF)
    val bool = mkUniqConst(BoolT1)
    val gAbs = mkUniqAbs(annotatedLetInF) // we have to wrap the parameterless body of G with a lambda expression
    val letInG = mkUniqLet("G", gAbs, bool)

    val listener = mock[TypeCheckerListener]
    expecting {
      // variable x has a parametric type
      listener.onTypeFound(xName.sourceRef.asInstanceOf[ExactRef], parser("a")).atLeastOnce()
      listener.onTypeFound(xNameInApp.sourceRef.asInstanceOf[ExactRef], parser("a")).atLeastOnce()
      // d has the same type!
      listener.onTypeFound(d.sourceRef.asInstanceOf[ExactRef], parser("a")).atLeastOnce()
      // xDomain is Set(a), the type a propagates
      listener.onTypeFound(xDomain.sourceRef.asInstanceOf[ExactRef], parser("Set(a)")).atLeastOnce()
      // This is the generic type of F
      listener.onTypeFound(fBody.sourceRef.asInstanceOf[ExactRef], parser("a => a")).atLeastOnce()
      listener.onTypeFound(setInF.sourceRef.asInstanceOf[ExactRef], parser("a"))
      listener.onTypeFound(fApp.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      listener.onTypeFound(fArg.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      // Igor: is it OK that the type below is not reported?
      //      listener.onTypeFound(letInF.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      // although the type of F is concrete here, the type of the let-in definition is parametric!
      listener.onTypeFound(fName.sourceRef.asInstanceOf[ExactRef], parser("Int => Int"))
      // reported types of G
      listener.onTypeFound(bool.sourceRef.asInstanceOf[ExactRef], parser("Bool"))
      listener.onTypeFound(gAbs.sourceRef.asInstanceOf[ExactRef], parser("() => Int")).atLeastOnce()
      listener.onTypeFound(letInG.sourceRef.asInstanceOf[ExactRef], parser("Bool"))
    }
    whenExecuting(listener) {
      val context = TypeContext.empty
      val computed = checker.compute(listener, context, letInG)
      assert(computed.contains(parser("Bool")))
    }
  }

  test("well-typed application of nullary let-in") {
    val recType = parser("[foo: Int, bar: Str]")
    val fType = parser("() => [foo: Int, bar: Str]")
    // let F == RecT1(...) in F
    val recRef = mkUniqConst(recType)
    // even a nullary let-in definition requires a lambda, but this lambda has no arguments
    val fBody = mkUniqAbs(recRef)
    val fName = mkUniqName("F")
    val fApp = mkUniqAppByName(fName)
    val letIn = mkUniqLet("F", fBody, fApp)

    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeFound(fName.sourceRef.asInstanceOf[ExactRef], fType)
      // the result of applying F is recType
      listener.onTypeFound(fApp.sourceRef.asInstanceOf[ExactRef], recType).atLeastOnce()
      // the type of the record
      listener.onTypeFound(recRef.sourceRef.asInstanceOf[ExactRef], recType).atLeastOnce()
      // the signature a => a gives us the polymorphic type for the definition of F
      listener.onTypeFound(fBody.sourceRef.asInstanceOf[ExactRef], fType).atLeastOnce()
      // interestingly, we do not infer the type of F at the application site
      //      listener.onTypeFound(fBody.tlaId, parser("Int => Int")).atLeastOnce()
      // the overall result of LET-IN
      listener.onTypeFound(letIn.sourceRef.asInstanceOf[ExactRef], recType).atLeastOnce()
    }
    whenExecuting(listener) {
      // we do not compute principal types here....
      val annotations = TypeContext("F" -> TlaType1Scheme(fType, Set.empty))
      val computed = checker.compute(listener, annotations, letIn)
      assert(computed.contains(recType))
    }
  }

  test("partial unification in application") {
    val oper = parser("Seq(a) => Set(a)")
    val arg = mkUniqConst(parser("a"))
    val app = mkUniqApp(Seq(oper), arg)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef],
          "An operator with the signature ((Seq(a)) => Set(a)) cannot be applied to the provided argument of type a")
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.isEmpty)
    }
  }

  test("sound unification in application") {
    val oper = parser("(a, Str) => Set(a)")
    val arg1 = mkUniqConst(parser("Int"))
    val arg2 = mkUniqConst(parser("b"))
    val app = mkUniqApp(Seq(oper), arg1, arg2)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(arg1.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      listener.onTypeFound(arg2.sourceRef.asInstanceOf[ExactRef], parser("Str")).atLeastOnce()
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("Set(Int)")).atLeastOnce()
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => Set(Int)")))
    }
  }

  test("CHOOSE") {
    // (((a => Bool) => a) (λ x ∈ Set(Int). x = Int))
    val xRef = mkUniqName("x")
    val int = mkUniqConst(parser("Int"))
    val eq = mkUniqApp(Seq(parser("(a, a) => Bool")), xRef, int)
    val xName = mkUniqName("x")
    val xDom = mkUniqConst(parser("Set(Int)"))
    val lambda = mkUniqAbs(eq, (xName, xDom))
    val oper = parser("(a => Bool) => a")
    val app = mkUniqApp(Seq(oper), lambda)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(xName.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      listener.onTypeFound(xDom.sourceRef.asInstanceOf[ExactRef], parser("Set(Int)")).atLeastOnce()
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      listener.onTypeFound(int.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      listener.onTypeFound(xRef.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      listener.onTypeFound(eq.sourceRef.asInstanceOf[ExactRef], parser("Bool")).atLeastOnce()
      listener.onTypeFound(lambda.sourceRef.asInstanceOf[ExactRef], parser("(Int) => Bool")).atLeastOnce()
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => Int")))
    }
  }

  test("unbounded CHOOSE") {
    // (((c => Bool) => c) (λ x ∈ Set(b). x = Int))
    val xRef = mkUniqName("x")
    val int = mkUniqConst(parser("Int"))
    val eq = mkUniqApp(Seq(parser("(a, a) => Bool")), xRef, int)
    val xDom = mkUniqConst(SetT1(VarT1("b")))
    val xName = mkUniqName("x")
    val lambda = mkUniqAbs(eq, (xName, xDom))
    val oper = parser("(c => Bool) => c")
    val app = mkUniqApp(Seq(oper), lambda)
    val wrapper = wrapWithLet(app)
    val listener = new DefaultTypeCheckerListener()
    val computed = checker.compute(listener, TypeContext.empty, wrapper)
    // Our better type checker propagates Int upwards, so we have a precise type here
    assert(computed.contains(parser("() => Int")))
  }

  test("record set constructor") {
    // [x: Set(Int), y: Set(Str)]
    val operType = parser("(Set(a), Set(b)) => Set([x: a, y: b])")
    val arg1 = mkUniqConst(parser("Set(Int)"))
    val arg2 = mkUniqConst(parser("Set(Str)"))
    val app = mkUniqApp(Seq(operType), arg1, arg2)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(arg1.sourceRef.asInstanceOf[ExactRef], parser("Set(Int)")).atLeastOnce()
      listener.onTypeFound(arg2.sourceRef.asInstanceOf[ExactRef], parser("Set(Str)")).atLeastOnce()
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("Set([x: Int, y: Str])")).atLeastOnce()
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => Set([x: Int, y: Str])")))
    }
  }

  test("record constructor (regression)") {
    // [x: Str, y: Int]
    val operType = parser("(a, b) => [x: a, y: b]")
    val arg1 = mkUniqConst(parser("Str"))
    val arg2 = mkUniqName("y")
    val app = mkUniqApp(Seq(operType), arg1, arg2)
    val listener = mock[TypeCheckerListener]
    val wrapper = wrapWithLet(app)
    expecting {
      listener.onTypeFound(arg1.sourceRef.asInstanceOf[ExactRef], parser("Str")).atLeastOnce()
      listener.onTypeFound(arg2.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("[x: Str, y: Int]")).atLeastOnce()
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext("y" -> TlaType1Scheme(IntT1, Set.empty)), wrapper)
      assert(computed.contains(parser("() => [x: Str, y: Int]")))
    }
  }

  test("DOMAIN f") {
    val operTypes = Seq(parser("(a -> b) => Set(a)"), parser("Seq(a) => Set(Int)"), parser("[] => Set(Str)"),
        parser("{} => Set(Int)"))
    val arg1 = mkUniqConst(parser("[foo: Int, bar: Bool]"))
    val app = mkUniqApp(operTypes, arg1)
    val wrapper = wrapWithLet(app)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeFound(arg1.sourceRef.asInstanceOf[ExactRef], parser("[foo: Int, bar: Bool]")).atLeastOnce()
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("Set(Str)")).atLeastOnce()
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => Set(Str)")))
    }
  }

  // this is the toughest expression that is produced by the TLA+ syntax
  test("recursive function") {
    //   (((a -> b) => (a => b)) => a -> b) (λ $recFun ∈ Set(c -> d). (λ x ∈ Set(Int). x))
    val operType = parser("((a -> b) => (a => b)) => a -> b")
    val recFunDom = mkUniqConst(parser("Set(c -> d)"))
    val xRef = mkUniqName("x")
    val xDom = mkUniqConst(parser("Set(Int)"))
    val xName = mkUniqName("x")
    val innerLambda = mkUniqAbs(xRef, (xName, xDom))
    val recFun = mkUniqName("$recFun")
    val outerLambda = mkUniqAbs(innerLambda, (recFun, recFunDom))
    val app = mkUniqApp(Seq(operType), outerLambda)
    val wrapper = wrapWithLet(app)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeFound(xName.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      listener.onTypeFound(recFun.sourceRef.asInstanceOf[ExactRef], parser("Int -> Int")).atLeastOnce()
      listener.onTypeFound(recFunDom.sourceRef.asInstanceOf[ExactRef], parser("Set(Int -> Int)")).atLeastOnce()
      listener.onTypeFound(xRef.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      listener.onTypeFound(xDom.sourceRef.asInstanceOf[ExactRef], parser("Set(Int)")).atLeastOnce()
      listener.onTypeFound(innerLambda.sourceRef.asInstanceOf[ExactRef], parser("Int => Int")).atLeastOnce()
      listener
        .onTypeFound(outerLambda.sourceRef.asInstanceOf[ExactRef], parser("(Int -> Int) => (Int => Int)"))
        .atLeastOnce()
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("Int -> Int")).atLeastOnce()
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => (Int -> Int)")))
    }
  }

  test("check type declaration") {
    val scopedEx = mkUniqName("foo")
    val typeDecl = mkUniqTypeDecl("foo", parser("Set(Int)"), scopedEx)
    val wrapper = wrapWithLet(typeDecl)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeFound(scopedEx.sourceRef.asInstanceOf[ExactRef], parser("Set(Int)")).atLeastOnce()
      listener.onTypeFound(typeDecl.sourceRef.asInstanceOf[ExactRef], parser("Set(Int)")).atLeastOnce()
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.contains(parser("() => Set(Int)")))
    }
  }

  test("rejected tuple syntax") {
    // Without a type annotation, it is impossible to choose between a tuple or a sequence.
    // <<Int, Int>> is rejected. Is it a tuple or a sequence? Use a type annotation.
    val seq = OperT1(Seq(IntT1, IntT1), SeqT1(IntT1))
    val tup = OperT1(Seq(IntT1, IntT1), TupT1(IntT1, IntT1))
    val app = mkUniqApp(Seq(seq, tup), mkUniqConst(IntT1), mkUniqConst(IntT1))
    val wrapper = wrapWithLet(app)

    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef],
          "Annotation required. Found 2 matching operator signatures ((Int, Int) => Seq(Int)) or ((Int, Int) => <<Int, Int>>) for arguments Int and Int")
      // consume any types for the wrapper and lambda
      consumeWrapperTypes(listener, wrapper)
    }
    whenExecuting(listener) {
      // we do not compute principal types here....
      val computed = checker.compute(listener, TypeContext.empty, wrapper)
      assert(computed.isEmpty)
    }
  }

  test("annotated tuple") {
    // use the annotation to resolve overloading by the resulting type

    // let F == <<Int, Int>> in F
    // without a type annotation, it is impossible to choose between a tuple or a sequence
    val seq = OperT1(Seq(IntT1, IntT1), SeqT1(IntT1))
    val tup = OperT1(Seq(IntT1, IntT1), TupT1(IntT1, IntT1))
    val intT = mkUniqConst(IntT1)
    val fBody = mkUniqApp(Seq(seq, tup), intT, intT)
    // for consistency of the expression language, we have to wrap the body with lambda in any case
    val lambda = mkUniqAbs(fBody)
    val fName = mkUniqName("F")
    val fApp = mkUniqAppByName(fName)
    val letIn = mkUniqLet("F", lambda, fApp)

    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeFound(fName.sourceRef.asInstanceOf[ExactRef], parser("() => <<Int, Int>>"))
      listener.onTypeFound(intT.sourceRef.asInstanceOf[ExactRef], parser("Int")).atLeastOnce()
      listener.onTypeFound(fBody.sourceRef.asInstanceOf[ExactRef], parser("<<Int, Int>>")).atLeastOnce()
      listener.onTypeFound(lambda.sourceRef.asInstanceOf[ExactRef], parser("() => <<Int, Int>>")).atLeastOnce()
      listener.onTypeFound(fApp.sourceRef.asInstanceOf[ExactRef], parser("<<Int, Int>>")).atLeastOnce()
      listener.onTypeFound(letIn.sourceRef.asInstanceOf[ExactRef], parser("<<Int, Int>>")).atLeastOnce()
    }
    whenExecuting(listener) {
      // we do not compute principal types here....
      val annotations = TypeContext("F" -> TlaType1Scheme(parser("<<Int, Int>>"), Set.empty))
      val computed = checker.compute(listener, annotations, letIn)
      assert(computed.contains(parser("<<Int, Int>>")))
    }
  }

  test("imprecise annotation") {
    // Test case for: https://github.com/informalsystems/apalache/issues/2102

    // let @type: (a, b) => Bool;
    //   LET F(x, y) == x = y in TRUE
    //
    // The principal type of F is (c, c) => Bool, which is more specific than (a, b) => Bool.
    val eq = parser("(c, c) => Bool")
    val x = mkUniqName("x")
    val y = mkUniqName("y")
    val fBody = mkUniqApp(Seq(eq), x, y)
    // introduce a lambda over the parameters x and y, whose domains are captured with type variables f and g
    val domX = mkUniqConst(VarT1("f"))
    val domY = mkUniqConst(VarT1("g"))
    val lambda = mkUniqAbs(fBody, (x, domX), (y, domY))
    val underLet = mkUniqConst(BoolT1)
    val letIn = mkUniqLet("F", lambda, underLet)
    val annotatedLetInF = mkUniqTypeDecl("F", parser("(a, b) => Bool"), letIn)
    val bool = mkUniqConst(BoolT1)
    val gAbs = mkUniqAbs(annotatedLetInF) // we have to wrap the parameterless body of G with a lambda expression
    val letInG = mkUniqLet("G", gAbs, bool)

    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeError(letIn.sourceRef.asInstanceOf[ExactRef],
          "F's type annotation ((a, b) => Bool) is too general, inferred: ((a, a) => Bool)")
      // consume all found types
      for (ex <- Seq(fBody, domX, domY, x, y, lambda, underLet, letIn, annotatedLetInF, bool, gAbs, letInG)) {
        listener.onTypeFound(EasyMock.eq(ex.sourceRef.asInstanceOf[ExactRef]), EasyMock.anyObject[TlaType1]).anyTimes()
      }
    }
    whenExecuting(listener) {
      // Notice that the annotation is imprecise! The type checker should complain.
      checker.compute(listener, TypeContext(), letInG)
    }
  }

  test("regression for principal types (issue #1259)") {
    val fooType = parser("(a -> b) => Bool")
    // \* @type: (a -> b) => Bool;
    // Foo(f) ==
    //   LET f2 == f IN
    //   LET d == DOMAIN f2 IN
    //   d = DOMAIN f

    // DOMAIN f
    val f = mkUniqName("f")
    val domF = mkUniqApp(Seq(parser("(x -> y) => Set(x)")), f)
    // d = DOMAIN f
    val d = mkUniqName("d")
    val appD = mkUniqAppByName(d)
    val eq = mkUniqApp(Seq(parser("(z, z) => Bool")), appD, domF)
    // DOMAIN f2
    val f2 = mkUniqName("f2")
    val appF2 = mkUniqAppByName(f2)
    val domF2 = mkUniqApp(Seq(parser("(i -> j) => Set(i)")), appF2)
    // LET d == DOMAIN f2 IN ...
    val lambdaD = mkUniqAbs(domF2)
    val letD = mkUniqLet("d", lambdaD, eq)
    // LET f2 == f IN ...
    val fAgain = mkUniqName("f")
    val lambdaF = mkUniqAbs(fAgain)
    val letF2 = mkUniqLet("f2", lambdaF, letD)
    // Foo(f) == ...
    val terminal = mkUniqConst(parser("Bool"))
    val fParam = mkUniqConst(parser("f"))
    val fOnceAgain = mkUniqName("f")
    val lambdaLetF2 = mkUniqAbs(letF2, (fOnceAgain, fParam))
    val letFoo = mkUniqLet("Foo", lambdaLetF2, terminal)

    val listener = mock[TypeCheckerListener]
    expecting {
      // the type of d should be () => Set(a)
      listener.onTypeFound(lambdaD.sourceRef.asInstanceOf[ExactRef], parser("() => Set(a)"))
      // we don't care about the rest
      listener
        .onTypeFound(EasyMock.not(EasyMock.eq(lambdaD.sourceRef.asInstanceOf[ExactRef])), EasyMock.anyObject[TlaType1])
        .anyTimes()
      // but no type errors
    }
    whenExecuting(listener) {
      // no failure
      val annotations = TypeContext("Foo" -> TlaType1Scheme(fooType, Set(0, 1)))
      checker.compute(listener, annotations, letFoo)
    }
  }
}
