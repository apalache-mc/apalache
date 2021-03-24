package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaOper}
import at.forsyte.apalache.tla.lir._
import TypedPredefs._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestOperAppToLetInDef extends FunSuite with BeforeAndAfterEach with TestingPredefs {

  private var wrapper = new OperAppToLetInDef(new UniqueNameGenerator, TrackerWithListeners())

  override def beforeEach(): Unit = {
    wrapper = new OperAppToLetInDef(new UniqueNameGenerator, TrackerWithListeners())
  }

  test("No app") {
    val types = Map("i" -> IntT1(), "S" -> SetT1(IntT1()), "b" -> BoolT1(), "t" -> TupT1(IntT1(), IntT1()))
    val exs = List(
        tla.plus(tla.int(1), tla.int(2)).typed(IntT1()),
        tla.tuple(n_x ? "i", n_y ? "b", n_z ? "i").typed(types, "t"),
        tla.exists(n_x ? "i", n_S ? "S", tla.gt(n_x ? "i", n_f ? "i") ? "b").typed(types, "b")
    )

    val tr = wrapper.wrap(Set.empty)
    val newExs = exs map tr
    assert(exs == newExs)
  }

  test("Single App") {
    val types = Map("i" -> IntT1(), "op" -> OperT1(Seq(IntT1(), IntT1()), IntT1()))
    val ex = tla.appOp(n_A ? "op", n_x ? "i", n_y ? "i").typed(types, "i")

    val tr1 = wrapper.wrap(Set.empty)
    val tr2 = wrapper.wrap(Set("A"))
    val newEx1 = tr1(ex)
    val newEx2 = tr2(ex)

    assert(newEx1 == ex)

    newEx2 match {
      case LetInEx(OperEx(TlaOper.apply, NameEx(someName)), TlaOperDecl(declName, Nil, defEx)) =>
        assert(declName == someName)
        assert(defEx == ex)

      case _ =>
        fail("Expected LetInEx(...)")
    }
  }

  test("Mixed") {
    val types = Map("i" -> IntT1(), "op" -> OperT1(Seq(IntT1(), IntT1()), IntT1()))
    val ex1 = tla.appOp(n_A ? "op", n_x ? "i", n_y ? "i").typed(types, "i")
    val ex2 = tla.appOp(n_B ? "op", n_x ? "i", n_y ? "i").typed(types, "i")
    val ex = tla.plus(ex1, ex2).typed(types, "i")

    val tr = wrapper.wrap(Set("A"))
    val newEx = tr(ex)

    newEx match {
      case OperEx(TlaArithOper.plus, exA, exB) =>
        exA match {
          case LetInEx(OperEx(TlaOper.apply, NameEx(someName)), TlaOperDecl(declName, Nil, defEx)) =>
            assert(declName == someName)
            assert(defEx == ex1)

          case _ =>
            fail("Expected LetInEx(...)")
        }
        assert(exB == ex2)

      case _ =>
        fail("Expected OperEx(...)")
    }
  }

}
