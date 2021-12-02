package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.{ConstT1, StrT1}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestModelValueHandler extends FunSuite {
  test("Pattern matching") {
    val s1 = "string"
    val s2 = "1_OF_A"
    val s3 = "1_OF_B"
    val s4 = "1_OF_lowercase"

    val f = ModelValueHandler.modelValueOrString _

    assert(f(s1) == StrT1())
    assert(f(s2) == ConstT1("A"))
    assert(f(s3) == ConstT1("B"))
    assert(f(s4) == StrT1())

  }

  test("Inversion") {
    val pairs = Seq(
        ("A", "1"),
        ("A", "2"),
        ("B", "one"),
        ("B", "two")
    )

    val ctr = ModelValueHandler.construct _
    val read = ModelValueHandler.modelValueOrString _
    val ti = ModelValueHandler.typeAndIndex _

    assert(
        pairs.forall(pa => read(ctr(pa)) == ConstT1(pa._1))
    )

    val values = Seq(
        ("A", "1"),
        ("A", "2"),
        ("B", "one"),
        ("B", "two")
    ) map { p => s"${p._2}_OF_${p._1}" }

    assert(
        values.forall(v => ti(v).map(x => ctr((x._1.name, x._2))).contains(v))
    )
  }

}
