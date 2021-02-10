package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaEx, IrGenerators, TlaOperDecl}
import org.scalacheck.Prop
import org.scalacheck.Prop.{falsified, forAll, passed}
import org.scalatest.prop.Checkers
import org.scalatest.{BeforeAndAfter, FunSuite}

/**
 * Tests of PrimePropagation.
 */
class TestPrimePropagation extends FunSuite with BeforeAndAfter with Checkers {

  import tla._

  private var transformer: PrimePropagation = _

  before {
    transformer = new PrimePropagation(new IdleTracker, Set("x", "y"))
  }

  test("a name should not be primed") {
    val input = name("x")
    val output = transformer(input)
    assert(output == input)
  }

  test("a constant should not be primed") {
    val input = name("N")
    val output = transformer(input)
    assert(output == input)
  }

  test("a primed variable stays primed") {
    val input = prime(name("x"))
    val output = transformer(input)
    assert(output == input)
  }

  test("a primed literal is de-primed") {
    val intEx = int(2021)
    val input = prime(intEx)
    val output = transformer(input)
    assert(intEx == output)
  }

  test("a primed constant is de-primed") {
    val const = name("N")
    val input = prime(const)
    val output = transformer(input)
    assert(const == output)
  }

  test("prime is propagated in operator") {
    val input = prime(appFun(name("x"), name("y")))
    val output = transformer(input)
    val expected = appFun(prime(name("x")), prime(name("y")))
    assert(expected == output)
  }

  test("prime is propagated in LET-IN") {
    val fooDecl = TlaOperDecl("Foo", List.empty, appFun(name("x"), name("y")))
    val letIn = LetInEx(appOp("Foo"), fooDecl)
    val input = prime(letIn)
    val output = transformer(input)
    val expectedDecl = TlaOperDecl("Foo", List.empty, appFun(prime(name("x")), prime(name("y"))))
    val expectedLetIn = LetInEx(appOp("Foo"), expectedDecl)
    assert(expectedLetIn == output)
  }

  private def onlyNamesArePrimed: TlaEx => Prop = {
    case OperEx(TlaActionOper.prime, NameEx(_)) =>
      passed

    case OperEx(TlaActionOper.prime, _*) =>
      falsified

    case OperEx(_, args @ _*) =>
      args.map(onlyNamesArePrimed).foldLeft(passed)(_ && _)

    case LetInEx(body, defs @ _*) =>
      defs.map(d => onlyNamesArePrimed(d.body)).foldLeft(onlyNamesArePrimed(body))(_ && _)

    case _ => passed
  }

  test("prime applies only to names after the transformation") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 10
    }

    val prop = {
      forAll(gens.genTlaEx(gens.simpleOperators ++ gens.arithOperators :+ TlaActionOper.prime)(Seq())) { ex =>
        onlyNamesArePrimed(transformer(ex))
      }
    }

    check(prop, minSuccessful(10000), sizeRange(10))
  }
}
