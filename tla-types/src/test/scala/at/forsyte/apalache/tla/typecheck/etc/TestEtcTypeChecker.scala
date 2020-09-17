package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.typecheck.parser.DefaultType1Parser
import org.junit.runner.RunWith
import org.scalatest.easymock.EasyMockSugar
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestEtcTypeChecker  extends FunSuite with EasyMockSugar with BeforeAndAfterEach with EtcBuilder {
  private val parser: Type1Parser = DefaultType1Parser
  private var checker: TypeChecker = _

  override protected def beforeEach(): Unit = {
    checker = new EtcTypeChecker()
  }

  test("check monotypes") {
    val mono = mkUniqConst(parser("Int -> Int"))
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeFound(mono.sourceRef.asInstanceOf[ExactRef], mono.polytype)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, mono)
      assert(computed.contains(mono.polytype))
    }
  }

  test("check names") {
    val expr = mkUniqName("foo")
    val listener = mock[TypeCheckerListener]
    val intSet = parser("Set(Int)")
    expecting {
      listener.onTypeFound(expr.sourceRef.asInstanceOf[ExactRef], intSet)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, new TypeContext(Map("foo" -> intSet)), expr)
      assert(computed.contains(intSet))
    }
  }

  test("well-typed application") {
    val oper = parser("Int => Int")
    val arg = mkUniqConst(IntT1())
    val app = mkUniqApp(Seq(oper), arg)
    val listener = mock[TypeCheckerListener]
    val int = IntT1()
    expecting {
      listener.onTypeFound(arg.sourceRef.asInstanceOf[ExactRef], int)
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], int)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, app)
      assert(computed.contains(int))
    }
  }

  test("ill-typed application") {
    val oper = parser("Int => Int")
    val arg = mkUniqConst(BoolT1())
    val app = mkUniqApp(Seq(oper), arg)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef], "No matching signature for argument type(s): Bool")
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, app)
      assert(computed.isEmpty)
    }
  }

  test("unresolved argument") {
    val oper = parser("a => Int")
    val arg = mkUniqConst(parser("b"))
    val app = mkUniqApp(Seq(oper), arg)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef],
        "Unresolved a in operator signature: (a) => Int")
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef],
        "No matching signature for argument type(s): b")
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, app)
      assert(computed.isEmpty)
    }
  }

  test("unresolved result") {
    val oper = parser("Int => a")
    val arg = mkUniqConst(IntT1())
    val app = mkUniqApp(Seq(oper), arg)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef],
        "Unresolved a in operator signature: (Int) => a")
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef],
        "No matching signature for argument type(s): Int")
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, app)
      assert(computed.isEmpty)
    }
  }

  test("one resolved, one unresolved") {
    val operTypes = Seq(parser("Int => a"), parser("Int => Bool"))
    val arg = mkUniqConst(IntT1())
    val app = mkUniqApp(operTypes, arg)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef],
        "Unresolved a in operator signature: (Int) => a")
      listener.onTypeFound(arg.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("Bool"))
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, app)
      // TODO: is this the expected behavior? The type checker goes through, although one signature had a typing issue
      assert(computed.contains(BoolT1()))
    }
  }

  test("multiple signatures") {
    val operTypes = Seq(parser("Int => Int"), parser("Bool => Bool"))
    val arg = mkUniqConst(IntT1())
    val app = mkUniqApp(operTypes, arg)
    val listener = mock[TypeCheckerListener]
    val int = IntT1()
    expecting {
      listener.onTypeFound(arg.sourceRef.asInstanceOf[ExactRef], int)
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], int)
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, app)
      assert(computed.contains(int))
    }
  }

  test("error: multiple signatures") {
    val operTypes = Seq(parser("a => Int"), parser("a => Bool"))
    val arg = mkUniqConst(IntT1())
    val app = mkUniqApp(operTypes, arg)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeError(app.sourceRef.asInstanceOf[ExactRef],
        "2 matching signatures for argument type(s): Int")
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, app)
      assert(computed.isEmpty)
    }
  }

  test("well-typed application by name") {
    val arg = mkUniqConst(IntT1())
    val app = mkUniqAppByName("F", arg)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeFound(arg.sourceRef.asInstanceOf[ExactRef], parser("Int"))
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef], parser("Int"))
    }
    whenExecuting(listener) {
      val operType = parser("Int => Int")
      val computed = checker.compute(listener, TypeContext("F" -> operType), app)
      assert(computed.contains(IntT1()))
    }
  }

  test("no upward errors on nested error") {
    val arg = mkUniqConst(BoolT1())
    val innerApp = mkUniqApp(Seq(parser("Int => Int")), arg)
    val outerApp = mkUniqApp(Seq(parser("Int => Int")), innerApp)

    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeError(innerApp.sourceRef.asInstanceOf[ExactRef],
        "No matching signature for argument type(s): Bool")
      // There is no error about outerApp. Otherwise, we would introduce a long string of errors.
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, outerApp)
      assert(computed.isEmpty)
    }
  }

  test("well-typed application of unary lambda") {
    val xDomain = mkUniqConst(parser("Set(Int)"))
    // lambda x \in Set(Int): Bool
    val lambda = mkUniqAbs(
      mkUniqConst(parser("Bool")),            // this is a predicate
      ("x", xDomain)  // the scope of the variable x, which is used in the predicate
    )/////
    val operType = parser("(a => Bool) => Set(a)")
    val app = mkUniqApp(Seq(operType), lambda)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeFound(xDomain.sourceRef.asInstanceOf[ExactRef],
        parser("Set(Int)")).atLeastOnce()
      listener.onTypeFound(lambda.sourceRef.asInstanceOf[ExactRef],
        parser("Int => Bool")).atLeastOnce()
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef],
        parser("Set(Int)")).atLeastOnce()
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, app)
      assert(computed.contains(parser("Set(Int)")))
    }
  }

  test("well-typed application of binary lambda") {
    val xDomain = mkUniqConst(parser("Set(Int)"))
    val yDomain = mkUniqConst(parser("Set(Str)"))
    // lambda x \in Set(Int), y \in Set(Str): Bool
    val lambda = mkUniqAbs(
      mkUniqConst(parser("Bool")),            // this is a predicate
      ("x", xDomain), // the scope of the variable x, which is used in the predicate
      ("y", yDomain)  // the scope of the variable y, which is used in the predicate
    )/////
    val operType = parser("((a, b) => Bool) => Set(<<a, b>>)")
    val app = mkUniqApp(Seq(operType), lambda)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeFound(xDomain.sourceRef.asInstanceOf[ExactRef],
        xDomain.polytype).atLeastOnce()
      listener.onTypeFound(yDomain.sourceRef.asInstanceOf[ExactRef],
        yDomain.polytype).atLeastOnce()
      listener.onTypeFound(lambda.sourceRef.asInstanceOf[ExactRef],
        parser("(Int, Str) => Bool")).atLeastOnce()
      listener.onTypeFound(app.sourceRef.asInstanceOf[ExactRef],
        parser("Set(<<Int, Str>>)")).atLeastOnce()
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, app)
      assert(computed.contains(parser("Set(<<Int, Str>>)")))
    }
  }

  test("ill-typed application of unary lambda") {
    // lambda x \in Int: Bool
    val lambda = mkUniqAbs(
      mkUniqConst(parser("Bool")),       // this is a predicate
      ("x", mkUniqConst(parser("Int")))  // the ill-typed scope of the variable x
    )/////
    val operType = parser("(a => Bool) => Set(a)")
    val app = mkUniqApp(Seq(operType), lambda)
    val listener = mock[TypeCheckerListener]
    expecting {
      listener.onTypeError(lambda.sourceRef.asInstanceOf[ExactRef],
        "Expected variable x to be bound by a set, found: Int")
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, app)
      assert(computed.isEmpty)
    }
  }

  test("well-typed application of let-in") {
    // let F == lambda x \in Set(a): x in F(Int)
    val xDomain = mkUniqConst(parser("Set(a)"))
    val xInF = mkUniqName("x")
    val fBody = mkUniqAbs(xInF, ("x", xDomain))
    val fArg = mkUniqConst(IntT1())
    val fApp = mkUniqAppByName("F", fArg)
    val letIn = mkUniqLet("F", fBody, fApp)

    val listener = mock[TypeCheckerListener]
    expecting {
      // the argument to F has the monotype Int
      listener.onTypeFound(fArg.sourceRef.asInstanceOf[ExactRef],
        parser("Int")).atLeastOnce()
      // the result of applying F(Int) is Int
      listener.onTypeFound(fApp.sourceRef.asInstanceOf[ExactRef],
        parser("Int")).atLeastOnce()
      // the signature a => a gives us the polymorhic type of x
      listener.onTypeFound(xInF.sourceRef.asInstanceOf[ExactRef],
        parser("a")).atLeastOnce()
      // the signature a => a gives us the polymorphic type of xDomain
      listener.onTypeFound(xDomain.sourceRef.asInstanceOf[ExactRef],
        parser("Set(a)")).atLeastOnce()
      // the signature a => a gives us the polymorphic type for the definition of F
      listener.onTypeFound(fBody.sourceRef.asInstanceOf[ExactRef],
        parser("a => a")).atLeastOnce()
      // interestingly, we do not infer the type of F at the application site
//      listener.onTypeFound(fBody.tlaId, parser("Int => Int")).atLeastOnce()
      // the overall result of LET-IN
      listener.onTypeFound(letIn.sourceRef.asInstanceOf[ExactRef],
        parser("Int")).atLeastOnce()
    }
    whenExecuting(listener) {
      // we do not compute principal types here....
      val annotations = TypeContext("F" -> parser("a => a"))
      val computed = checker.compute(listener, annotations, letIn)
      assert(computed.contains(parser("Int")))
    }
  }

  // for monotypes, we can easily infer the types of the definitions
  test("inferring a let-in definition") {
    // let F == lambda x \in Set(Int): x in F(Int)
    val xDomain = mkUniqConst(parser("Set(Int)"))
    val xInF = mkUniqName("x")
    val fBody = mkUniqAbs(xInF, ("x", xDomain))
    val fArg = mkUniqConst(IntT1())
    val fApp = mkUniqAppByName("F", fArg)
    val letIn = mkUniqLet("F", fBody, fApp)

    val listener = mock[TypeCheckerListener]
    expecting {
      // the argument to F has the monotype Int
      listener.onTypeFound(fArg.sourceRef.asInstanceOf[ExactRef],
        parser("Int")).atLeastOnce()
      // the result of applying F(Int) is Int
      listener.onTypeFound(fApp.sourceRef.asInstanceOf[ExactRef],
        parser("Int")).atLeastOnce()
      // xDomain is Set(Int), it is trivial to infer the type
      listener.onTypeFound(xDomain.sourceRef.asInstanceOf[ExactRef],
        parser("Set(Int)")).atLeastOnce()
      // we infer x: Int from x \in Set(Int)
      listener.onTypeFound(xInF.sourceRef.asInstanceOf[ExactRef],
        parser("Int")).atLeastOnce()
      // in this case, we trivially infer the type of F
      listener.onTypeFound(fBody.sourceRef.asInstanceOf[ExactRef],
        parser("Int => Int")).atLeastOnce()
      // interestingly, we do not infer the type of F at the application site
//      listener.onTypeFound(fBody.tlaId, parser("Int => Int")).atLeastOnce()
      // the overall result of LET-IN
      listener.onTypeFound(letIn.sourceRef.asInstanceOf[ExactRef],
        parser("Int")).atLeastOnce()
    }
    whenExecuting(listener) {
      val computed = checker.compute(listener, TypeContext.empty, letIn)
      assert(computed.contains(parser("Int")))
    }
  }

  test("well-typed application of nullary let-in") {
    val recType = parser("[foo: Int, bar: Str]")
    val fType = parser("() => [foo: Int, bar: Str]")
    // let F == RecT1(...) in F
    val recRef = mkUniqConst(recType)
    // even a nullary let-in definition requires a lambda, but this lambda has no arguments
    val fBody = mkUniqAbs(recRef)
    val fApp = mkUniqAppByName("F")
    val letIn = mkUniqLet("F", fBody, fApp)

    val listener = mock[TypeCheckerListener]
    expecting {
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
      val annotations = TypeContext("F" -> fType)
      val computed = checker.compute(listener, annotations, letIn)
      assert(computed.contains(recType))
    }
  }
}