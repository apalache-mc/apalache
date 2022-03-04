package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.{ConstT1, IntT1, SeqT1, SetT1, StrT1, TupT1, TypingException}
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.easymock.EasyMockSugar
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestConstSubstitution extends AnyFunSuite with EasyMockSugar with EtcBuilder {

  test("simple substitution") {
    val sub = ConstSubstitution(Map("A" -> IntT1()))
    val (result, _) = sub(SetT1(ConstT1("A")))
    val expected = SetT1(IntT1())
    assert(expected == result)
  }

  test("transitive substitution") {
    val sub = ConstSubstitution(Map("A" -> SeqT1(ConstT1("B")), "B" -> SetT1(ConstT1("C")), "C" -> StrT1()))
    val closure = sub.closure()
    val (result, _) = closure(TupT1(ConstT1("A"), ConstT1("B"), ConstT1("C")))
    val expected = TupT1(SeqT1(SetT1(StrT1())), SetT1(StrT1()), StrT1())
    assert(expected == result)
  }

  test("cyclic substitution") {
    val sub = ConstSubstitution(Map("A" -> ConstT1("B"), "B" -> ConstT1("A")))
    // Though the substitution is cyclic, the closure terminates by substituting values for A and B.
    // However, it produces the result, where some aliases are still undefined.
    assertThrows[TypingException](sub.closure())
  }
}
