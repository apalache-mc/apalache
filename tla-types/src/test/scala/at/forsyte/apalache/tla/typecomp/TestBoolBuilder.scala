package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestBoolBuilder extends BuilderTest {

  def argGen(n: Int): Seq[TBuilderInstruction] = Seq.fill(n)(builder.bool(true))

  def testCmpOKAndMistyped[T](
      args: Seq[TBuilderInstruction],
      oper: TlaBoolOper,
      cmp: PureTypeComputation,
      eval: Seq[TBuilderInstruction] => TBuilderInstruction): Unit = {

    val builtArgs = args.map(build)
    val res = cmp(builtArgs)

    assert(res.contains(BoolT1))

    val resEx = eval(args)

    assert(resEx.eqTyped(OperEx(oper, builtArgs: _*)(Typed(BoolT1))))

    val badY: TBuilderInstruction = builder.str("a")
    val badArgs = badY +: args.tail

    assertThrows[TBuilderTypeException] {
      build(eval(badArgs))
    }
  }

  test("and") {
    val oper = TlaBoolOper.and
    (1 to 5).foreach { i =>
      testCmpOKAndMistyped(
          argGen(i),
          oper,
          cmpFactory.computationFromSignature(oper),
          builder.and(_: _*),
      )
    }
  }

  test("or") {
    val oper = TlaBoolOper.or
    (1 to 5).foreach { i =>
      testCmpOKAndMistyped(
          argGen(i),
          oper,
          cmpFactory.computationFromSignature(oper),
          builder.or(_: _*),
      )
    }
  }

  test("not") {
    val oper = TlaBoolOper.not
    testCmpOKAndMistyped(
        argGen(1),
        oper,
        cmpFactory.computationFromSignature(oper),
        { case Seq(e) => builder.not(e) },
    )
  }

  test("impl") {
    val oper = TlaBoolOper.implies
    testCmpOKAndMistyped(
        argGen(2),
        oper,
        cmpFactory.computationFromSignature(oper),
        { case Seq(a, b) => builder.impl(a, b) },
    )
  }

  test("equiv") {
    val oper = TlaBoolOper.equiv
    testCmpOKAndMistyped(
        argGen(2),
        oper,
        cmpFactory.computationFromSignature(oper),
        { case Seq(a, b) => builder.equiv(a, b) },
    )
  }

  def testQuant(
      oper: TlaBoolOper,
      methodE: Either[(TBuilderInstruction, TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction, (
              TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction]): Unit = {
    val xBool = builder.name("x", BoolT1)
    val xInt = builder.name("x", IntT1)

    val sBool = builder.name("S", SetT1(BoolT1))
    val sInt = builder.name("S", SetT1(IntT1))

    val (okW, typeErrorW, scopeErrorW, expected) = methodE match {
      case Left(boundQuant) =>
        val okW = boundQuant(xBool, sBool, xBool)

        val typeErrorW = boundQuant(xBool, sInt, xBool)

        val scopeErrorW = boundQuant(xInt, sInt, xBool)

        val expected = OperEx(
            oper,
            NameEx("x")(Typed(BoolT1)),
            NameEx("S")(Typed(SetT1(BoolT1))),
            NameEx("x")(Typed(BoolT1)),
        )(Typed(BoolT1))

        (okW, typeErrorW, scopeErrorW, expected)
      case Right(unboundQuant) =>
        val okW = unboundQuant(xBool, xBool)

        val typeErrorW = unboundQuant(xInt, xInt)

        val scopeErrorW = unboundQuant(xInt, xBool)

        val expected = OperEx(
            oper,
            NameEx("x")(Typed(BoolT1)),
            NameEx("x")(Typed(BoolT1)),
        )(Typed(BoolT1))

        (okW, typeErrorW, scopeErrorW, expected)
    }

    assert(okW.eqTyped(expected))

    assertThrows[TBuilderTypeException] {
      build(typeErrorW)
    }

    assertThrows[TBuilderScopeException] {
      build(scopeErrorW)
    }
  }

  test("forall3") {
    testQuant(TlaBoolOper.forall, Left(builder.forall))
  }

  test("forall2") {
    testQuant(TlaBoolOper.forallUnbounded, Right(builder.forall))
  }

  test("exists3") {
    testQuant(TlaBoolOper.exists, Left(builder.exists))
  }

  test("exists2") {
    testQuant(TlaBoolOper.existsUnbounded, Right(builder.exists))
  }

}
