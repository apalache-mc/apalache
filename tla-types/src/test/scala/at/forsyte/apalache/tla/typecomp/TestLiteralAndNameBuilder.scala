package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestLiteralAndNameBuilder extends BuilderTest {

  test("literals") {

    val oneEx: TlaEx = builder.int(1)

    assert(oneEx.eqTyped(ValEx(TlaInt(1))(Typed(IntT1))))

    val xEx: TlaEx = builder.str("x")

    assert(xEx.eqTyped(ValEx(TlaStr("x"))(Typed(StrT1))))
    assertThrows[TBuilderTypeException] {
      build(builder.str("1_OF_X"))
    }

    val trueEx: TlaEx = builder.bool(true)

    assert(trueEx.eqTyped(ValEx(TlaBool(true))(Typed(BoolT1))))

    val v1: TlaEx = builder.constParsed("v_OF_A")
    val v2: TlaEx = builder.const("v", ConstT1("A"))

    assert(v1.eqTyped(v2))
    assert(v2.eqTyped(ValEx(TlaStr("v_OF_A"))(Typed(ConstT1("A")))))

    assertThrows[TBuilderTypeException] {
      build(builder.constParsed("x"))
    }
    assertThrows[TBuilderTypeException] {
      build(builder.const("1_OF_A", ConstT1("A")))
    }
    assertThrows[TBuilderTypeException] {
      build(builder.const("1_OF_A", ConstT1("B")))
    }

  }

  test("names and scope") {

    val xInt = builder.name("x", IntT1)

    val xBool = builder.name("x", BoolT1)

    // ok separately
    val xIntEx = build(xInt)

    assert(xIntEx.eqTyped(NameEx("x")(Typed(IntT1))))

    val xBoolEx = build(xBool)

    assert(xBoolEx.eqTyped(NameEx("x")(Typed(BoolT1))))

    // Throw if in same scope
    assertThrows[TBuilderScopeException] {
      val both = for {
        _ <- xInt
        _ <- xBool
      } yield ()
      both.run(TBuilderContext.empty)
    }

  }
}
