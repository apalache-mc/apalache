package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.{OperParam, VarT1}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.typecheck.etc.{EqClass, Substitution}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestTypeSubstitutor extends FunSuite with BeforeAndAfterEach {

  import tla._

  private val parser = DefaultType1Parser

  private val types =
    Map("b" -> parser("Bool"), "F" -> parser("a => <<a, a>>"), "a" -> parser("a"), "ii" -> parser("Int -> Int"),
        "Fii" -> parser("(Int -> Int) => <<Int -> Int, Int -> Int>>"), "aa" -> parser("<<a, a>>"),
        "ii2" -> parser("<<Int -> Int, Int -> Int>>"))

  override def beforeEach(): Unit = {}

  test("""a name""") {
    val input = name("x").typed(VarT1(0))
    val sub = Substitution(EqClass(0) -> parser("Int -> Int"))
    val output = new TypeSubstitutor(new IdleTracker, sub)(input)
    val expected = tla.name("x").typed(parser("Int -> Int"))
    assert(expected.eqTyped(output))
  }

  test("""an integer""") {
    val input = int(1).typed(parser("Int"))
    val sub = Substitution(EqClass(0) -> parser("Int -> Int"))
    val output = new TypeSubstitutor(new IdleTracker, sub)(input)
    assert(input.eqTyped(output))
  }

  test("""a Boolean""") {
    val input = bool(true).typed(parser("Bool"))
    val sub = Substitution(EqClass(0) -> parser("Int -> Int"))
    val output = new TypeSubstitutor(new IdleTracker, sub)(input)
    assert(input.eqTyped(output))
  }

  test("""a string""") {
    val input = str("abc").typed(parser("Str"))
    val sub = Substitution(EqClass(0) -> parser("Int -> Int"))
    val output = new TypeSubstitutor(new IdleTracker, sub)(input)
    assert(input.eqTyped(output))
  }

  test("""an operator""") {
    val input = appOp(name("F") ? "F", name("x") ? "a").typed(types, "aa")
    val sub = Substitution(EqClass(0) -> parser("Int -> Int"))
    val output = new TypeSubstitutor(new IdleTracker, sub)(input)
    val expected = appOp(name("F") ? "Fii", name("x") ? "ii").typed(types, "ii2")
    assert(expected.eqTyped(output))
  }

  test("""a let-in""") {
    // F(x)
    val FofX = appOp(name("F") ? "F", name("x") ? "a") ? "aa"
    // <<x, x>>
    val pair = tuple(name("x") ? "a", name("x") ? "a").typed(types, "aa")
    val declOfF = declOp("F", pair, OperParam("x")).typedOperDecl(types, "F")
    // LET F(x) == <<x, x>> IN F(x)
    val input = letIn(FofX, declOfF).typed(types, "aa")
    val sub = Substitution(EqClass(0) -> parser("Int -> Int"))
    val output = new TypeSubstitutor(new IdleTracker, sub)(input)
    // concrete types
    val concreteFofX = appOp(name("F") ? "Fii", name("x") ? "ii") ? "ii2"
    val concretePair = tuple(name("x") ? "ii", name("x") ? "ii").typed(types, "ii2")
    val concreteDeclOfF = declOp("F", concretePair, OperParam("x")).typedOperDecl(types, "Fii")
    val expected = letIn(concreteFofX, concreteDeclOfF).typed(types, "ii2")
    assert(expected.eqTyped(output))
  }
}
