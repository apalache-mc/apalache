package at.forsyte.apalache.tla.lir

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import UntypedPredefs._

@RunWith(classOf[JUnitRunner])
class TestAux extends FunSuite with TestingPredefs {

  test("Test aux::collectSegments") {

    val ar0Decl1 = TlaOperDecl("X", List.empty, n_x)
    val ar0Decl2 = TlaOperDecl("Y", List.empty, n_y)
    val ar0Decl3 = TlaOperDecl("Z", List.empty, n_z)

    val arGe0Decl1 = TlaOperDecl("A", List(SimpleFormalParam("t")), n_a)
    val arGe0Decl2 = TlaOperDecl("B", List(SimpleFormalParam("t")), n_b)
    val arGe0Decl3 = TlaOperDecl("C", List(SimpleFormalParam("t")), n_c)

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
        pa5
    )
    val cmp = expected map { case (k, v) =>
      (v, aux.collectSegments(k))
    }
    cmp foreach { case (ex, act) =>
      assert(ex == act)
    }
  }
}
