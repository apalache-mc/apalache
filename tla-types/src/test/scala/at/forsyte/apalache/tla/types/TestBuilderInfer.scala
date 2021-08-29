package at.forsyte.apalache.tla.types

import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck.TypeInfer._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
 * Tests the expression builder in conjunction with semi-automatic type inference.
 */
@RunWith(classOf[JUnitRunner])
class TestBuilderInfer extends FunSuite {
  // import all names from the Builder object, so we can easily construct an expression

  import at.forsyte.apalache.tla.lir.convenience.tla._

  private val parser = DefaultType1Parser

  test("infer: int") {
    val output = int(42).inferType()
    val expected = ValEx(TlaInt(42))(Typed(IntT1()))
    assertEqWithType(expected, output)
  }

  test("infer: bool") {
    val output = bool(true).inferType()
    val expected = ValEx(TlaBool(true))(Typed(BoolT1()))
    assertEqWithType(expected, output)
  }

  test("infer: str") {
    val output = str("hello").inferType()
    val expected = ValEx(TlaStr("hello"))(Typed(StrT1()))
    assertEqWithType(expected, output)
  }

  test("infer: annotated name") {
    // A name should be annotated.
    // We do not call `inferType` here, as the expression is built by the call to `as`.
    val output = name("x") as IntT1()
    val expected = NameEx("x")(Typed(IntT1()))
    assertEqWithType(expected, output)
  }

  test("unannotated name") {
    // It is impossible to guess the name type in a bottom-up manner
    assertThrows[BuilderError](name("x").inferType())
  }

  test("infer: x = y") {
    val output = eql(int(1), name("x") as IntT1()).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("type error in x = y") {
    assertThrows[BuilderError](eql(int(1), name("x") as BoolT1()).inferType())
  }

  test("infer: x /= y") {
    val output = neql(int(1), name("x") as IntT1()).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("infer: F(x, y)") {
    val ftype = parser("(Int, Str) => Bool")
    val output = appOp(name("F") as ftype, int(1), str("foo")).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("infer: -x") {
    val output = uminus(int(1)).inferType()
    assert(Typed(IntT1()) == output.typeTag)
  }

  test("infer: x + y") {
    val output = plus(int(1), int(2)).inferType()
    assert(Typed(IntT1()) == output.typeTag)
  }

  test("infer: x - y") {
    val output = minus(int(4), int(2)).inferType()
    assert(Typed(IntT1()) == output.typeTag)
  }

  test("infer: x * y") {
    val output = mult(int(4), int(2)).inferType()
    assert(Typed(IntT1()) == output.typeTag)
  }

  test("""infer: x \div y""") {
    val output = div(int(4), int(2)).inferType()
    assert(Typed(IntT1()) == output.typeTag)
  }
  test("""infer: x / y""") {
    val output = rDiv(name("x") as RealT1(), name("y") as RealT1()).inferType()
    assert(Typed(RealT1()) == output.typeTag)
  }

  test("""infer: x % y""") {
    val output = mod(int(4), int(2)).inferType()
    assert(Typed(IntT1()) == output.typeTag)
  }

  test("infer: x^y") {
    val output = exp(int(4), int(2)).inferType()
    assert(Typed(IntT1()) == output.typeTag)
  }

  test("infer: x > y") {
    val output = gt(int(4), int(2)).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("infer: x >= y") {
    val output = ge(int(4), int(2)).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("infer: x < y") {
    val output = lt(int(4), int(2)).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("infer: x <= y") {
    val output = le(int(4), int(2)).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("infer: let-in") {
    val ftype = parser("Int => Bool")
    val letBody = appOp(name("F") as ftype, int(1))
    val bodyOfF = plus(name("x") as IntT1(), int(2)).inferType()
    val declOfF = declOp("F", bodyOfF, OperParam("x")) as ftype
    val output = letIn(letBody, declOfF).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("infer: A <=> B") {
    val output = equiv(bool(false), bool(true)).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("infer: A => B") {
    val output = impl(bool(false), bool(true)).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("""infer: A /\ B""") {
    val output = and(bool(false), bool(true)).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("""infer: A \/ B""") {
    val output = or(bool(false), bool(true)).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("infer: ~A") {
    val output = not(bool(false)).inferType()
    assert(Typed(BoolT1()) == output.typeTag)
  }

  test("infer: 1..3") {
    val input = dotdot(int(1), int(3))
    val output = input.inferType()
    assert(Typed(parser("Set(Int)")) == output.typeTag)
  }

  test("infer error: {}") {
    assertThrows[BuilderError](enumSet().inferType())
  }

  test("infer: { 1, 2 }") {
    val input = enumSet(int(1), int(2))
    val output = input.inferType()
    assert(Typed(parser("Set(Int)")) == output.typeTag)
  }

  test("infer: [S -> T]") {
    val intSet = parser("Set(Int)")
    val boolSet = parser("Set(Bool)")
    val input = funSet(name("S") as intSet, name("T") as boolSet)
    val output = input.inferType()
    assert(Typed(parser("Set(Int -> Bool)")) == output.typeTag)
  }

  test("infer: [x: S, y: T]") {
    val S = name("S") as parser("Set(Int)")
    val T = name("T") as parser("Set(Bool)")
    val input = recSet(str("x"), S, str("y"), T)
    val output = input.inferType()
    assert(Typed(parser("Set([x: Int, y: Bool])")) == output.typeTag)
  }

  test("infer: Seq(S)") {
    val intSet = parser("Set(Int)")
    val input = seqSet(name("S") as intSet)
    val output = input.inferType()
    assert(Typed(parser("Set(Seq(Int))")) == output.typeTag)
  }

  test("""infer: x in S""") {
    val input = in(name("x") as parser("Int"), name("S") as parser("Set(Int)"))
    val output = input.inferType()
    assert(Typed(parser("Bool")) == output.typeTag)
  }

  test("""infer: x notin S""") {
    val input = notin(name("x") as parser("Int"), name("S") as parser("Set(Int)"))
    val output = input.inferType()
    assert(Typed(parser("Bool")) == output.typeTag)
  }

  test("""infer: S subseteq T""") {
    val intSet = parser("Set(Int)")
    val input = subseteq(name("S") as intSet, name("T") as intSet)
    val output = input.inferType()
    assert(Typed(parser("Bool")) == output.typeTag)
  }

  test("infer: SUBSET S") {
    val intSet = parser("Set(Int)")
    val input = powSet(name("S") as intSet)
    val output = input.inferType()
    assert(Typed(parser("Set(Set(Int))")) == output.typeTag)
  }

  test("infer: UNION S") {
    val intIntSet = parser("Set(Set(Int))")
    val input = union(name("S") as intIntSet)
    val output = input.inferType()
    assert(Typed(parser("Set(Int)")) == output.typeTag)
  }

  test("""infer: S union T""") {
    val intSet = parser("Set(Int)")
    val input = cup(name("S") as intSet, name("T") as intSet)
    val output = input.inferType()
    assert(Typed(intSet) == output.typeTag)
  }

  test("""infer: S intersect T""") {
    val intSet = parser("Set(Int)")
    val input = cap(name("S") as intSet, name("T") as intSet)
    val output = input.inferType()
    assert(Typed(intSet) == output.typeTag)
  }

  test("""infer: S setminus T""") {
    val intSet = parser("Set(Int)")
    val input = setminus(name("S") as intSet, name("T") as intSet)
    val output = input.inferType()
    assert(Typed(intSet) == output.typeTag)
  }

  test("""infer: S times T""") {
    val intSet = parser("Set(Int)")
    val input = times(name("S") as intSet, name("T") as intSet)
    val output = input.inferType()
    assert(Typed(parser("Set(<<Int, Int>>)")) == output.typeTag)
  }

  test("infer: [x |-> S, y |-> T]") {
    val S = name("S") as parser("Set(Int)")
    val T = name("T") as parser("Set(Bool)")
    val input = enumFun(str("x"), S, str("y"), T)
    val output = input.inferType()
    assert(Typed(parser("[x: Set(Int), y: Set(Bool)]")) == output.typeTag)
  }

  test("infer error: <<>>") {
    assertThrows[BuilderError](tuple().inferType())
  }

  test("infer: <<1, TRUE>>") {
    val input = tuple(int(1), bool(true))
    val output = input.inferType()
    assert(Typed(parser("<<Int, Bool>>")) == output.typeTag)
  }

  test("infer error: <<1, 2>>") {
    // There is no way to choose between a sequence or a tuple here.
    // The user has to write a manual annotation: e as t
    val input = tuple(int(1), int(2))
    assertThrows[BuilderError](input.inferType())
  }

  test("infer: f[TRUE]") {
    val input = appFun(name("f") as parser("Bool -> Int"), bool(true))
    val output = input.inferType()
    assert(Typed(parser("Int")) == output.typeTag)
  }

  test("infer: seq[3]") {
    val input = appFun(name("seq") as parser("Seq(Bool)"), int(3))
    val output = input.inferType()
    assert(Typed(parser("Bool")) == output.typeTag)
  }

  test("infer: tuple[3]") {
    val input = appFun(name("tuple") as parser("<<Int, Bool, Str>>"), int(3))
    val output = input.inferType()
    assert(Typed(parser("Str")) == output.typeTag)
  }

  test("infer: rec.x") {
    val rec = name("rec") as parser("[x: Int, y: Bool]")
    val input = appFun(rec, str("x"))
    val output = input.inferType()
    assert(Typed(parser("Int")) == output.typeTag)
  }

  test("infer: DOMAIN f") {
    val input = dom(name("f") as parser("Int -> Str"))
    val output = input.inferType()
    assert(Typed(parser("Set(Int)")) == output.typeTag)
  }

  test("infer: DOMAIN tuple") {
    val input = dom(name("tuple") as parser("<<Int, Bool, Str>>"))
    val output = input.inferType()
    assert(Typed(parser("Set(Int)")) == output.typeTag)
  }

  test("infer: DOMAIN seq") {
    val input = dom(name("seq") as parser("Seq(Bool)"))
    val output = input.inferType()
    assert(Typed(parser("Set(Int)")) == output.typeTag)
  }

  test("infer: DOMAIN rec") {
    val input = dom(name("rec") as parser("[x: Int, y: Bool]"))
    val output = input.inferType()
    assert(Typed(parser("Set(Str)")) == output.typeTag)
  }

  test("infer error: [ f EXCEPT ![2] = TRUE ]") {
    // EXCEPT is too hard to handle automatically, because the indices have to be wrapped into a tuple.
    // This requires a second layer of inference, which we want to avoid.
    // You have to supply a manual annotation: `e as t`.
    val ftype = parser("Int -> Bool")
    val accessor = tuple(int(2)) as IntT1()
    val input = except(name("f") as ftype, accessor, bool(true))
    assertThrows[BuilderError](input.inferType())
  }

  // TODO: CHOOSE, E, A, filter, map, fun ctor, rec fun ctor, rec fun ref

  private def assertEqWithType(output: TlaEx, expected: TlaEx): Unit = {
    assert(expected == output)
    assert(expected.typeTag == output.typeTag)
  }
}
