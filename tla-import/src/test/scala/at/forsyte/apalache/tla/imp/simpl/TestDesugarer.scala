package at.forsyte.apalache.tla.imp.simpl

import at.forsyte.apalache.tla.lir.convenience._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDesugarer extends FunSuite {
  test("chain 2 excepts") {
    // [f EXCEPT ![i][j] = e]
    val highCalories =
      tla.except(tla.name("f"), tla.tuple(tla.name("i"), tla.name("j")), tla.name("e"))
    val desugarer = new Desugarer
    val sugarFree = desugarer.transform(highCalories)
    // becomes [ f EXCEPT ![i] = [f[i] EXCEPT ![j] = e] ]
    val expected =
      tla.except(
        tla.name("f"),
        tla.tuple(tla.name("i")),
        tla.except(
          tla.appFun(tla.name("f"), tla.name("i")),
          tla.tuple(tla.name("j")),
          tla.name("e")))

    assert(expected == sugarFree)
  }

  test("chain 3 excepts") {
    // [f EXCEPT ![i][j][k] = e]
    val highCalories =
      tla.except(
        tla.name("f"),
        tla.tuple(tla.name("i"), tla.name("j"), tla.name("k")),
        tla.name("e"))
    val desugarer = new Desugarer
    val sugarFree = desugarer.transform(highCalories)
    // becomes [ f EXCEPT ![i] = [f[i] EXCEPT ![j] = [f[i][j] EXCEPT ![k] = e] ] ]
    val expected = tla.except(
      tla.name("f"),
      tla.tuple(tla.name("i")),
      tla.except(
        tla.appFun(tla.name("f"), tla.name("i")),
        tla.tuple(tla.name("j")),
        tla.except(
          tla.appFun(
            tla.appFun(tla.name("f"),
                       tla.name("i")),
              tla.name("j")),
          tla.tuple(tla.name("k")),
          tla.name("e"))))

    assert(expected == sugarFree)
  }

  test("unfold UNCHANGED <<x, <<y, z>> >> to UNCHANGED <<x, y, z>>") {
    // This is an idiom that was probably introduced by Diego Ongaro in Raft.
    // There is no added value in this construct, so it is just sugar.
    // So, we do the transformation right here.
    val unchanged = tla.unchangedTup(tla.name("x"), tla.tuple(tla.name("y"), tla.name("z")))
    val sugarFree = new Desugarer().transform(unchanged)
    val expected = tla.unchangedTup(tla.name("x"), tla.name("y"), tla.name("z"))
    assert(expected == sugarFree)
  }
}
