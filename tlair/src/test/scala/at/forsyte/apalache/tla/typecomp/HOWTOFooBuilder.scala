package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

/**
 * This is an example test, for an operator `Foo` described in the "HOW TO WRITE A NEW METHOD" guide in
 * [[ScopedBuilder]] and the "HOW TO WRITE A NEW TEST" guide in [[BuilderTest]].
 */
@RunWith(classOf[JUnitRunner])
class HOWTOFooBuilder extends BuilderTest {

  // Our mock operator
  object foo extends ApalacheOper {
    override def name: String = "Foo"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (100, 100)
  }

  // We know the signature to be
  // (a, a -> b) => b
  val fooSig: (TlaOper, Signature) = signatureMapEntry(foo, { case Seq(a, FunT1(aa, b)) if a == aa => b })
  // We're not adding to TypeComputationFactory, but this is how we _would have_ extended it
  val mockSignatureMap: SignatureMap = Map(fooSig)

  /**
   * The type-safe, scope-unsafe builder.foo is implemented via
   * [[BuilderUtil.composeAndValidateTypes composeAndValidateTypes]].
   *
   * This is how [[unsafe.ProtoBuilder.buildBySignatureLookup buildBySignatureLookup]] is implemented (we can't use that
   * method without adding foo to [[TypeComputationFactory]])
   */
  def unsafeBuilderDotFoo(x: TlaEx, y: TlaEx): TlaEx =
    composeAndValidateTypes(foo, mockSignatureMap(foo), x, y)

  /** The type-safe, scope-unsafe builder.foo is implemented via [[BuilderUtil.binaryFromUnsafe binaryFromUnsafe]] */
  def builderDotFoo(x: TBuilderInstruction, y: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(x, y)(unsafeBuilderDotFoo)

  test("foo") {
    // builder.foo takes 2 arguments, each one is a TBuilderInstruction
    type T = (TBuilderInstruction, TBuilderInstruction)
    // Foo has the signature (a, a -> b) => b, which is parameterized by 2 TlaType1 values (a, b)
    // We want to test arguments to builder.foo, for all kinds of a, b
    type TParam = (TlaType1, TlaType1)

    // Given type parameters (a,b), our arguments have types a and a -> b
    def mkWellTyped(tparam: TParam): T = {
      val (a, b) = tparam
      (
          builder.name("x", a),
          builder.name("y", FunT1(a, b)),
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (a, b) = tparam
      Seq(
          // (c, a -> b) is ill-typed, if c /= b
          (
              builder.name("x", InvalidTypeMethods.differentFrom(a)),
              builder.name("y", FunT1(a, b)),
          ),
          // (a, f) is ill-typed, if f is not a function type
          (
              builder.name("x", a),
              builder.name("y", InvalidTypeMethods.notApplicative),
          ),
          // (a, c -> b) is ill-typed, if c /= b
          (
              builder.name("x", a),
              builder.name("y", FunT1(InvalidTypeMethods.differentFrom(a), b)),
          ),
//          The following is _not_ ill-typed:
//          (
//              builder.name("x", a),
//              builder.name("y", FunT1(a, InvalidTypeMethods.differentFrom(b))),
//          ),
//          Since b isn't checked against any other argument, unlike a, if we swap b with some c
//          we get arguments with types a and a -> c, which is still valid w.r.t. the signature of foo, and would
//          return some value of type c.
      )
    }

    // We expect the result of builder.foo(x: a,y: a -> b) to be OperEx(foo, x, y)(Typed(b))
    def resultIsExpected = expectEqTyped[TParam, T](
        foo,
        mkWellTyped,
        ToSeq.binary,
        { case (_, b) => b },
    )

    // We run this test over combinations of (a,b) produced by doubleTypeGen
    checkRun(Generators.doubleTypeGen)(
        runBinary(
            builderDotFoo,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

}
