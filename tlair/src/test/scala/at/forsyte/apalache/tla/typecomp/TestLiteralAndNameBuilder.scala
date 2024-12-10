package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.ModelValueHandler
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

@RunWith(classOf[JUnitRunner])
class TestLiteralAndNameBuilder extends BuilderTest {

  // Literal builders have no ill-typed arguments, only malformed ones
  def mkIllTyped[A, B](@unused tparam: A): Seq[B] = Seq.empty

  test("int") {
    type T = BigInt

    def mkWellTyped(i: Int): T = i // implicit cast Int -> BigInt

    def resultIsExpected(i: Int)(resEx: TBuilderResult): Boolean = resEx.eqTyped(ValEx(TlaInt(i))(Typed(IntT1)))

    checkRun(Generators.intGen)(
        runUnary(
            builder.int,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("str") {
    type T = String

    def mkWellTyped(s: String): T = s

    def resultIsExpected(s: String)(resEx: TBuilderResult): Boolean = resEx.eqTyped(ValEx(TlaStr(s))(Typed(StrT1)))

    checkRun(Generators.nonEmptyStrGen)(
        runUnary(
            builder.str,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // throws on uninterpreted sorts
    assertThrows[TBuilderTypeException] {
      build(builder.str("1_OF_X"))
    }

  }

  test("bool") {
    type T = Boolean

    def mkWellTyped(b: Boolean): T = b

    def resultIsExpected(b: Boolean)(resEx: TBuilderResult): Boolean = resEx.eqTyped(ValEx(TlaBool(b))(Typed(BoolT1)))

    checkRun(Generators.boolGen)(
        runUnary(
            builder.bool,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("const") {
    type T1 = (String, ConstT1)
    type TParam = (String, ConstT1)

    def mkWellTyped1(tparam: TParam): T1 = tparam

    def resultIsExpected1(tparam: TParam)(resEx: TBuilderResult): Boolean = {
      val (index, constT) = tparam
      val fullName = ModelValueHandler.construct(constT.name, index)
      resEx.eqTyped(ValEx(TlaStr(fullName))(Typed(constT)))
    }

    checkRun(Generators.uninterpretedIndexAndTypeGen)(
        runBinary(
            builder.const,
            mkWellTyped1,
            mkIllTyped,
            resultIsExpected1,
        )
    )

    // Throws on ambiguous index
    assertThrows[TBuilderTypeException] {
      build(builder.const("1_OF_A", ConstT1("A")))
    }
    assertThrows[TBuilderTypeException] {
      build(builder.const("1_OF_A", ConstT1("B")))
    }

    type T2 = String

    def mkWellTyped2(s: String): T2 = s

    def resultIsExpected2(s: String)(resEx: TBuilderResult): Boolean =
      ModelValueHandler.typeAndIndex(s).exists { case (constT, _) =>
        resEx.eqTyped(ValEx(TlaStr(s))(Typed(constT)))
      }

    checkRun(Generators.uninterpretedLiteralGen)(
        runUnary(
            builder.constParsed,
            mkWellTyped2,
            mkIllTyped,
            resultIsExpected2,
        )
    )

    // throws on non-uninterpreted-literal
    assertThrows[TBuilderTypeException] {
      build(builder.constParsed("x"))
    }
  }

  test("names and scope") {
    type T = (String, TlaType1)
    type TParam = (String, TlaType1)

    def mkWellTyped(tparam: TParam): T = tparam

    def resultIsExpected(tparam: TParam)(resEx: TBuilderResult): Boolean = {
      val (name, tt) = tparam
      resEx.eqTyped(NameEx(name)(Typed(tt)))
    }

    checkRun(Generators.strAndTypeGen)(
        runBinary(
            builder.name,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // Throw on scope violations
    assertThrows[TBuilderScopeException] {
      build(
          for {
            _ <- builder.name("x", IntT1)
            _ <- builder.name("x", BoolT1)
          } yield ()
      )
    }

    // Should not throw with polymorphic names
    build(
        for {
          _ <- builder.polymorphicName("x", IntT1)
          _ <- builder.polymorphicName("x", BoolT1)
        } yield ()
    )
  }
}
