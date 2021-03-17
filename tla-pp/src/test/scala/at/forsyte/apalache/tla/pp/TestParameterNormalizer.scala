package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.typecheck.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck.{IntT1, OperT1}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestParameterNormalizer extends FunSuite with BeforeAndAfterEach with TestingPredefs {

  private val noTracker = TrackerWithListeners()
  val decisionFn: TlaOperDecl => Boolean = { _ => true }
  var parNorm = new ParameterNormalizer(new UniqueNameGenerator, noTracker, decisionFn)

  override def beforeEach(): Unit = {
    parNorm = new ParameterNormalizer(new UniqueNameGenerator, noTracker, decisionFn)
  }

  test("Nullary: No-op") {

    // A == 1
    val input = tla
      .declOp("A", tla.int(1))
      .typedOperDecl(OperT1(Seq(), IntT1()))

    val output = parNorm.normalizeDeclaration(input)

    assert(output == input && output.typeTag == input.typeTag)
  }

  test("Simple parameter") {
    val types = Map("i" -> IntT1(), "A" -> OperT1(Seq(IntT1()), IntT1()), "P" -> OperT1(Seq(), IntT1()))
    // A(p) == p
    val input = tla
      .declOp("A", tla.name("p") ? "i", "p")
      .typedOperDecl(types, "A")

    // A(p) ==
    //   LET new == p IN
    //     new
    val output = parNorm.normalizeDeclaration(input)

    output match {
      case d @ TlaOperDecl(name, List(SimpleFormalParam(p)), body) =>
        assert(input.typeTag == d.typeTag)

        body match {
          case ex1 @ LetInEx(letInBody, TlaOperDecl(newName, Nil, NameEx(paramName))) =>
            assert(name != newName)
            assert(p == paramName)
            assert(Typed(IntT1()) == ex1.typeTag)

            letInBody match {
              case ex2 @ OperEx(TlaOper.apply, nested @ NameEx(nestedName)) =>
                assert(Typed(IntT1()) == ex2.typeTag)
                assert(nestedName == newName)
                assert(Typed(types("P")) == nested.typeTag)

              case _ =>
                fail("expected OperEx")
            }

          case _ =>
            fail("expected LetInEx")
        }

      case _ =>
        fail("expected TlaOperDecl")
    }
  }

  test("HO parameter") {
    val types = Map("i" -> IntT1(), "T" -> OperT1(Seq(IntT1()), IntT1()),
        "A" -> OperT1(Seq(OperT1(Seq(IntT1()), IntT1())), IntT1()))

    // A(T(_)) == T(0)
    val input = tla
      .declOp("A", tla.appOp(n_T, tla.int(0)) ? "i", ("T", 1))
      .typedOperDecl(types, "A")

    val output = parNorm.normalizeDeclaration(input)

    // A(T(_)) ==
    //  LET NewName(p) == T(p) IN
    //    NewName(0)
    output match {
      case d @ TlaOperDecl(name, List(OperFormalParam(opName, 1)), body) =>
        assert(input.typeTag == d.typeTag)

        body match {
          case letin @ LetInEx(letInBody, TlaOperDecl(newName, List(SimpleFormalParam(intermediateParam)),
                      appex @ OperEx(TlaOper.apply, nex @ NameEx(appliedOperName), NameEx(arg)))) =>
            assert(opName == appliedOperName)
            assert(arg == intermediateParam)
            assert(Typed(IntT1()) == letin.typeTag)
            assert(Typed(IntT1()) == appex.typeTag)
            assert(Typed(types("T")) == nex.typeTag)

            letInBody match {
              case appex2 @ OperEx(TlaOper.apply, nex2 @ NameEx(innerName), arg2) =>
                assert(newName == innerName)
                assert(tla.int(0).typed() == arg2)
                assert(Typed(IntT1()) == appex2.typeTag)
                assert(Typed(types("T")) == nex2.typeTag)

              case _ => fail("Expected OperEx")
            }

          case _ => fail("expected LetInEx")
        }

      case _ =>
        fail("expected TlaOperDecl")
    }
  }

}
