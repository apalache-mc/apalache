package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import TypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

import scala.math.BigInt

@RunWith(classOf[JUnitRunner])
class TestUnroller extends FunSuite with BeforeAndAfterEach with TestingPredefs {

  private val noTracker = new IdleTracker()
  private var unroller = new Unroller(new UniqueNameGenerator, noTracker, new IncrementalRenaming(noTracker))

  override def beforeEach(): Unit = {
    unroller = new Unroller(new UniqueNameGenerator, noTracker, new IncrementalRenaming(noTracker))
  }

  def exAsDecl(pa: (String, TlaEx)): TlaOperDecl = tla
    .declOp(pa._1, pa._2)
    .typedOperDecl(OperT1(Seq(), IntT1()))

  test("No-op") {
    val strToInt = OperT1(Seq(StrT1()), IntT1())
    val types = Map("b" -> BoolT1(), "i" -> IntT1(), "T" -> strToInt)
    val tDecl = tla
      .declOp("T", tla.name("p").typed(StrT1()), "p")
      .typedOperDecl(strToInt)
    val dBody = tla
      .letIn(tla.appOp(n_T ? "T", tla.str("abc")) ? "i", tDecl)
      .typed(types, "i")
    val cBody = tla
      .and(n_x ? "i", n_P ? "b")
      .typed(Map("b" -> BoolT1(), "i" -> IntT1()), "b")
    val decls = Seq[(String, TlaEx)](
        ("A", tla.str("1").typed()),
        ("B", tla.int(0).typed()),
        ("C", cBody),
        ("D", dBody)
    ) map exAsDecl

    val module = new TlaModule("M", decls)

    val unrolled = unroller(module)

    assert(module.declarations == unrolled.declarations)
  }

  test("0 step: ParamNormalForm") {
    val strToInt = OperT1(Seq(StrT1()), IntT1())
    val types = Map("b" -> BoolT1(), "i" -> IntT1(), "s" -> StrT1(), "T" -> strToInt)
    val name = "A"

    val aBody = tla
      .appOp(n_A ? "T", n_p ? "s")
      .typed(types, "i")
    // A(p) == A(p)
    val recDecl = tla
      .declOp(name, aBody, "p")
      .typedOperDecl(strToInt)
    recDecl.isRecursive = true

    val defaultVal: BigInt = 42

    val decls = recDecl +: (Seq[(String, TlaEx)](
        (Unroller.UNROLL_TIMES_PREFIX + name, tla.int(0).typed(IntT1())),
        (Unroller.UNROLL_DEFAULT_PREFIX + name, tla.bigInt(defaultVal.intValue).typed(IntT1()))
    ) map exAsDecl)

    val module = new TlaModule("M", decls)

    val unrolled = unroller(module)

    val newAOpt = unrolled.operDeclarations.find(_.name == name)

    newAOpt match {
      case Some(d @ TlaOperDecl(_, _, body)) =>
        assert(!d.isRecursive)
        body match {
          case LetInEx(letBody, TlaOperDecl(_, Nil, declBody)) =>
            assert(tla.bigInt(defaultVal).typed() == letBody)
            assert(tla.name("p").typed(IntT1()) == declBody)
            true

          case _ => false
        }
    }
  }

  test("1 step: Nontrivial inlining") {
    // prepare the inputs
    val intToInt = OperT1(Seq(IntT1()), IntT1())
    val types = Map("b" -> BoolT1(), "i" -> IntT1(), "s" -> StrT1(), "T" -> intToInt)
    val declarationName = "A"

    // A(p)
    val aBody = tla
      .appOp(tla.name(declarationName) ? "T", n_p ? "i")
      .typed(types, "i")
    // A(p) == A(p)
    val recDecl = tla
      .declOp(declarationName, aBody, "p")
      .typedOperDecl(intToInt)
    recDecl.isRecursive = true

    val defaultVal: BigInt = 42

    val decls = recDecl +: (Seq[(String, TlaEx)](
        (Unroller.UNROLL_TIMES_PREFIX + declarationName, tla.int(1).typed(IntT1())),
        (Unroller.UNROLL_DEFAULT_PREFIX + declarationName, tla.int(defaultVal.intValue).typed(IntT1()))
    ) map exAsDecl)

    val module = new TlaModule("M", decls)

    // call the unroller that we are testing
    val unrolled = unroller(module)

    // test the outputs
    val newAOpt = unrolled.operDeclarations.find(_.name == declarationName)

    newAOpt match {
      case Some(d @ TlaOperDecl(_, _, body)) =>
        assert(!d.isRecursive)
        assert(Typed(IntT1()) == d.body.typeTag)

        body match {
          case LetInEx(paramNormalBody, TlaOperDecl(uniqueName, Nil, NameEx("p"))) =>
            assert(Typed(IntT1()) == paramNormalBody.typeTag)

            paramNormalBody match {
              case LetInEx(defaultBody, TlaOperDecl(_, Nil, OperEx(TlaOper.apply, NameEx(defaultName)))) =>
                assert(tla.bigInt(defaultVal).typed() == defaultBody)
                assert(uniqueName == defaultName)
                assert(Typed(IntT1()) == defaultBody.typeTag)

              case _ =>
                fail("Expected second LetInEx")
            }

          case _ =>
            fail("Expected first LetInEx")
        }

      case None =>
        fail("Expected Some(TlaOperDecl(...))")
    }

  }

  test("Recursive LET-IN inside non-recursive operator") {
    val intToInt = OperT1(Seq(IntT1()), IntT1())
    val types = Map("b" -> BoolT1(), "i" -> IntT1(), "s" -> StrT1(), "T" -> intToInt, "X" -> OperT1(Seq(), IntT1()))
    val letInOpName = "A"

    val aBody = tla
      .appOp(n_A ? "T", n_p ? "i")
      .typed(types, "i")
    // A(p) == A(p)
    val recDecl = tla
      .declOp(letInOpName, aBody, "p")
      .typedOperDecl(intToInt)
    recDecl.isRecursive = true

    val appEx = tla
      .appOp(tla.name("A") ? "T", tla.int(99) ? "i")
      .typed(types, "i")
    // X == LET A(p) == A(p) IN A(99)
    val nonRecDecl = tla
      .declOp("X", tla.letIn(appEx, recDecl).typed(types, "i"))
      .typedOperDecl(types, "X")

    val defaultVal: BigInt = 42

    val decls = nonRecDecl +: (Seq[(String, TlaEx)](
        (Unroller.UNROLL_TIMES_PREFIX + letInOpName, tla.int(1).typed(IntT1())),
        (Unroller.UNROLL_DEFAULT_PREFIX + letInOpName, tla.int(defaultVal.intValue).typed(IntT1()))
    ) map exAsDecl)

    val module = new TlaModule("M", decls)

    val unrolled = unroller(module)

    val newXOpt = unrolled.operDeclarations.find(_.name == "X")

    // The test is: Does an embedded LET-IN get unrolled in the same way as a top-level declaration

    // reset Renaming
    unroller = new Unroller(new UniqueNameGenerator, noTracker, new IncrementalRenaming(noTracker))

    val altDecls = recDecl +: (Seq[(String, TlaEx)](
        (Unroller.UNROLL_TIMES_PREFIX + letInOpName, tla.int(1).typed(IntT1())),
        (Unroller.UNROLL_DEFAULT_PREFIX + letInOpName, tla.bigInt(defaultVal.intValue).typed(IntT1()))
    ) map exAsDecl)

    val altModule = new TlaModule("N", altDecls)
    val altUnrolled = unroller(altModule)

    val aUnrolledOpt = altUnrolled.operDeclarations.find(_.name == letInOpName)

    assert(aUnrolledOpt.nonEmpty)

    val aUnrolledBody = aUnrolledOpt.get.body

    // explicit matching and assertions instead of smart and error-prone computations
    newXOpt match {
      case Some(TlaOperDecl(_, _, body)) =>
        body match {
          case LetInEx(letBody, TlaOperDecl(declName, params, unrolled)) =>
            assert(appEx == letBody)
            assert(letInOpName == declName)
            assert(List(SimpleFormalParam("p")) == params)
            assert(aUnrolledBody == unrolled)

          case _ =>
            fail("The unrolled body does not match the pattern")
        }

      case None =>
        fail("Expected TlaOperDecl")
    }
  }

}
