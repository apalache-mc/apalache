package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfter
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestBoolBuilder extends AnyFunSuite with BeforeAndAfter {
  var varPool = new TypeVarPool()
  var sigGen = new SignatureGenerator(varPool)
  var builder = new ScopedBuilder(sigGen)

  before {
    varPool = new TypeVarPool()
    sigGen = new SignatureGenerator(varPool)
    builder = new ScopedBuilder(sigGen)
  }

  def argGen(n: Int) = Seq.fill(n)(builder.bool(true))

  def testCmpUntypedAndMistyped[T](
      args: Seq[BuilderWrapper],
      oper: TlaBoolOper,
      cmp: pureTypeComputation,
      eval: Seq[BuilderWrapper] => BuilderWrapper) {

    val builtArgs = args.map(build)
    val res = cmp(builtArgs)

    assert(res.contains(BoolT1()))

    val resEx = eval(args)

    assert(resEx.eqTyped(OperEx(oper, builtArgs: _*)(Typed(BoolT1()))))

    val badY = builder.str("a")
    val badArgs = badY +: args.tail

    assertThrows[BuilderTypeException] {
      build(eval(badArgs))
    }
  }

  test("and") {
    val oper = TlaBoolOper.and
    (1 to 5).foreach { i =>
      testCmpUntypedAndMistyped(
          argGen(i),
          oper,
          sigGen.computationFromSignature(oper, i),
          builder.and(_: _*),
      )
    }
  }

  test("or") {
    val oper = TlaBoolOper.or
    (1 to 5).foreach { i =>
      testCmpUntypedAndMistyped(
          argGen(i),
          oper,
          sigGen.computationFromSignature(oper, i),
          builder.or(_: _*),
      )
    }
  }

  test("forall") {
    val mBuilder = new ScopedBuilder(sigGen)

    val xBool = mBuilder.name("x", BoolT1())
    val xInt = mBuilder.name("x", IntT1())

    val sBool = mBuilder.name("S", SetT1(BoolT1()))
    val sInt = mBuilder.name("S", SetT1(IntT1()))

    val okForall = builder.forall(xBool, sBool, xBool)

    val typeErrorForall = builder.forall(xBool, sInt, xBool)

    val scopeErrorForall = builder.forall(xInt, sInt, xBool)

    assert(
        okForall.eqTyped(
            OperEx(
                TlaBoolOper.forall,
                NameEx("x")(Typed(BoolT1())),
                NameEx("S")(Typed(SetT1(BoolT1()))),
                NameEx("x")(Typed(BoolT1())),
            )(Typed(BoolT1()))
        )
    )

    assertThrows[BuilderTypeException] {
      build(typeErrorForall)
    }

    assertThrows[BuilderScopeException] {
      build(scopeErrorForall)
    }

  }

}
