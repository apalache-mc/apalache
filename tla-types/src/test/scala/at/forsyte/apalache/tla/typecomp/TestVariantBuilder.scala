package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.VariantOper
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestVariantBuilder extends BuilderTest {

  implicit val tagGen: Gen[String] = Gen.alphaStr

  implicit val variantGen: Gen[VariantT1] = for {
    n <- Gen.choose(1, 5)
    flds <- Gen.listOfN(n, Gen.zip(tagGen, singleTypeGen))
  } yield VariantT1(RowT1(SortedMap(flds: _*), None))

  def variantGenWithMandatoryEntry(mandatoryEntry: (String, TlaType1)): Gen[VariantT1] = variantGen.map { variantT =>
    VariantT1(RowT1(variantT.row.fieldTypes + mandatoryEntry, None))
  }

  def variantGenWithMandatoryField(mandatoryField: String): Gen[VariantT1] =
    singleTypeGen.flatMap { fldT =>
      variantGenWithMandatoryEntry(mandatoryField -> fldT)
    }

  test("variant") {
    type T = (String, TBuilderInstruction, VariantT1)
    type TParam = (String, TlaType1, VariantT1)

    implicit val gen: Gen[TParam] = for {
      tagName <- tagGen
      valT <- singleTypeGen
      variantT <- variantGenWithMandatoryEntry(tagName -> valT)
    } yield (tagName, valT, variantT)

    // Variant(tagName, val) : varT
    def mkWellTyped(tparam: TParam): T = {
      val (tagName, t, varT) = tparam
      (
          tagName,
          builder.name("val", t),
          varT,
      )
    }

    // If tagName -> t is not in varT, that's an IllegalArgument exception, tested later
    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (tagName, t, varT) = tparam
      Seq(
          (
              tagName,
              builder.name("val", InvalidTypeMethods.differentFrom(t)),
              varT,
          )
      )
    }

    def resultIsExpected = expectEqTyped[TParam, T](
        VariantOper.variant,
        mkWellTyped,
        { case (a, b, _) => Seq(builder.str(a), b) },
        { case (_, _, t) => t },
    )

    checkRun(
        runTernary(
            builder.variant,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // throws on malformed variant type
    assertThrows[IllegalArgumentException] {
      build(
          builder.variant(
              "x",
              builder.name("a", IntT1),
              VariantT1(RowT1("y" -> IntT1)),
          )
      )
    }

  }

  test("variantFilter") {
    type T = (String, TBuilderInstruction)
    type TParam = (String, VariantT1)

    implicit val gen: Gen[TParam] = for {
      tagName <- tagGen
      variantT <- variantGenWithMandatoryField(tagName)
    } yield (tagName, variantT)

    // VariantFilter(tagName, set)
    def mkWellTyped(tparam: TParam): T = {
      val (tagName, varT) = tparam
      (
          tagName,
          builder.name("set", SetT1(varT)),
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (tagName, varT) = tparam
      Seq(
          (
              tagName,
              builder.name("set", InvalidTypeMethods.notSet),
          ),
          (
              tagName,
              builder.name("set", SetT1(InvalidTypeMethods.differentFrom(varT))),
          ),
          (
              tagName,
              builder.name("set", SetT1(VariantT1(RowT1(varT.row.fieldTypes - tagName, None)))),
          ),
      )
    }

    def resultIsExpected = expectEqTyped[TParam, T](
        VariantOper.variantFilter,
        mkWellTyped,
        { case (a, b) => Seq(builder.str(a), b) },
        { case (tagName, t) => SetT1(t.row.fieldTypes(tagName)) },
    )

    checkRun(
        runBinary(
            builder.variantFilter,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("variantTag") {
    type T = TBuilderInstruction
    type TParam = VariantT1

    // VariantTag(ex)
    def mkWellTyped(tparam: TParam): T = builder.name("ex", tparam)

    def mkIllTyped(@unused tparam: TParam): Seq[T] =
      Seq(
          builder.name("set", InvalidTypeMethods.notVariant)
      )

    def resultIsExpected = expectEqTyped[TParam, T](
        VariantOper.variantTag,
        mkWellTyped,
        Seq(_),
        { _ => StrT1 },
    )

    checkRun(
        runUnary(
            builder.variantTag,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("variantGetOrElse") {
    type T = (String, TBuilderInstruction, TBuilderInstruction)
    type TParam = (String, TlaType1, VariantT1)

    implicit val gen: Gen[TParam] = for {
      tagName <- tagGen
      valT <- singleTypeGen
      variantT <- variantGenWithMandatoryEntry(tagName -> valT)
    } yield (tagName, valT, variantT)

    // VariantGetOrElse(tagName, v, default)
    def mkWellTyped(tparam: TParam): T = {
      val (tagName, t, varT) = tparam
      (
          tagName,
          builder.name("v", varT),
          builder.name("default", t),
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (tagName, t, varT) = tparam
      Seq(
          (
              tagName,
              builder.name("v", InvalidTypeMethods.notVariant),
              builder.name("default", t),
          ),
          (
              tagName,
              builder.name("v", VariantT1(RowT1(varT.row.fieldTypes - tagName, None))),
              builder.name("default", t),
          ),
          (
              tagName,
              builder.name("v", varT),
              builder.name("default", InvalidTypeMethods.differentFrom(t)),
          ),
      )
    }

    def resultIsExpected = expectEqTyped[TParam, T](
        VariantOper.variantGetOrElse,
        mkWellTyped,
        { case (a, b, c) => Seq(builder.str(a), b, c) },
        { case (_, t, _) => t },
    )

    checkRun(
        runTernary(
            builder.variantGetOrElse,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("variantGetUnsafe") {
    type T = (String, TBuilderInstruction)
    type TParam = (String, VariantT1)

    implicit val gen: Gen[TParam] = for {
      tagName <- tagGen
      variantT <- variantGenWithMandatoryField(tagName)
    } yield (tagName, variantT)

    // VariantGetUnsafe(tagName, v)
    def mkWellTyped(tparam: TParam): T = {
      val (tagName, varT) = tparam
      (
          tagName,
          builder.name("v", varT),
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (tagName, varT) = tparam
      Seq(
          (
              tagName,
              builder.name("v", InvalidTypeMethods.notVariant),
          ),
          (
              tagName,
              builder.name("v", VariantT1(RowT1(varT.row.fieldTypes - tagName, None))),
          ),
      )
    }

    def resultIsExpected = expectEqTyped[TParam, T](
        VariantOper.variantGetUnsafe,
        mkWellTyped,
        { case (a, b) => Seq(builder.str(a), b) },
        { case (tagName, varT) => varT.row.fieldTypes(tagName) },
    )

    checkRun(
        runBinary(
            builder.variantGetUnsafe,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

}
