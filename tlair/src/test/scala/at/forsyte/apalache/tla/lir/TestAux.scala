package at.forsyte.apalache.tla.lir

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import at.forsyte.apalache.tla.lir.convenience.tla
import UntypedPredefs._

@RunWith(classOf[JUnitRunner])
class TestAux extends AnyFunSuite {

  test("Test aux::collectSegments") {

    val ar0Decl1 = TlaOperDecl("X", List.empty, tla.name("x"))
    val ar0Decl2 = TlaOperDecl("Y", List.empty, tla.name("y"))

    val arGe0Decl1 = TlaOperDecl("A", List(OperParam("t")), tla.name("a"))
    val arGe0Decl2 = TlaOperDecl("B", List(OperParam("t")), tla.name("b"))
    val arGe0Decl3 = TlaOperDecl("C", List(OperParam("t")), tla.name("c"))

    val pa1 =
      List(ar0Decl1) ->
        List(List(ar0Decl1))
    val pa2 =
      List(ar0Decl1, ar0Decl2) ->
        List(List(ar0Decl1, ar0Decl2))
    val pa3 =
      List(arGe0Decl1, ar0Decl1) ->
        List(List(arGe0Decl1), List(ar0Decl1))
    val pa4 =
      List(arGe0Decl1, arGe0Decl2) ->
        List(List(arGe0Decl1, arGe0Decl2))
    val pa5 =
      List(arGe0Decl1, arGe0Decl2, ar0Decl1, ar0Decl2, arGe0Decl3) ->
        List(List(arGe0Decl1, arGe0Decl2), List(ar0Decl1, ar0Decl2), List(arGe0Decl3))

    val expected = Seq(
        pa1,
        pa2,
        pa3,
        pa4,
        pa5,
    )
    val cmp = expected.map { case (k, v) =>
      (v, aux.collectSegments(k))
    }
    cmp.foreach { case (ex, act) =>
      assert(ex == act)
    }
  }
}
