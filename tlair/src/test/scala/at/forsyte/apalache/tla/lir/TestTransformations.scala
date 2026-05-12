package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.transformations.decorateWithPrime
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatest.Outcome

import java.io.{File, FileOutputStream, PrintStream}

@RunWith(classOf[JUnitRunner])
class TestTransformations extends AnyFunSuite {

  override protected def withFixture(test: NoArgTest): Outcome = {
    // Tmp file to capture the noisy stdout from these tests
    // otherwise they pollut stdout on our CI making it hard to see failures
    val tmp = File.createTempFile("tlair-test-output-", ".tmp")
    tmp.deleteOnExit()

    try {
      System.setOut(new PrintStream(new FileOutputStream(tmp)))
      super.withFixture(test)
    } finally {
      System.setOut(System.out)
    }

  }

  import tla._

  test("Test Prime") {
    val vars: Set[String] = Set(
        "x",
        "a",
    )
    val transformation = decorateWithPrime(vars, new IdleTracker())

    val a = tla.name("a")
    val x = tla.name("x")
    val y = tla.name("y")

    val pa1: (TlaEx, TlaEx) = x.untyped() -> prime(x).untyped()
    val pa2: (TlaEx, TlaEx) = y.untyped() -> y.untyped()
    val pa3 = prime(x).untyped() -> prime(x).untyped()
    val pa4 = and(x, y, prime(a)).untyped() -> and(prime(x), y, prime(a)).untyped()

    val expected = Seq(
        pa1,
        pa2,
        pa3,
        pa4,
    )
    val cmp = expected.map { case (k, v) =>
      (v, transformation(k))
    }
    cmp.foreach { case (ex, act) =>
      assert(ex == act)
    }
  }

  test("Test Flatten") {
    val transformation = Flatten(new IdleTracker())

    val A = tla.name("A")
    val a = tla.name("a")
    val b = tla.name("b")
    val c = tla.name("c")
    val d = tla.name("d")
    val e = tla.name("e")
    val f = tla.name("f")
    val g = tla.name("g")
    val h = NameEx("h")
    val x = tla.name("x")
    val y = tla.name("y")
    val z = tla.name("z")

    val pa1: (TlaEx, TlaEx) = x.untyped() -> x.untyped()
    val pa2 = and(x, and(y, z)).untyped() -> and(x, y, z).untyped()
    val pa3 = or(x, or(y, z)).untyped() -> or(x, y, z).untyped()
    val pa4 = or(x, and(y, z)).untyped() -> or(x, and(y, z)).untyped()
    val pa5 = and(
        and(
            or(
                or(a, b),
                or(c, d),
            )
        ),
        and(
            or(
                or(e, f),
                or(g, h),
            )
        ),
    ).untyped() -> and(
        or(a, b, c, d),
        or(e, f, g, h),
    ).untyped()
    val pa6 = enumSet(or(x, and(y, z))).untyped() -> enumSet(or(x, and(y, z))).untyped()
    val pa7 = letIn(
        appOp(A),
        declOp("A", int(1)).untypedOperDecl(),
    ).untyped() -> letIn(
        appOp(A),
        declOp("A", int(1)).untypedOperDecl(),
    ).untyped()

    val pa8 = letIn(
        appOp(A),
        declOp("A", or(x, or(y, z))).untypedOperDecl(),
    ).untyped() -> letIn(
        appOp(A),
        declOp("A", or(x, y, z)).untypedOperDecl(),
    ).untyped()

    val expected = Seq(
        pa1,
        pa2,
        pa3,
        pa4,
        pa5,
        pa6,
        pa7,
        pa8,
    )
    val cmp = expected.map { case (k, v) =>
      (v, transformation(k))
    }
    cmp.foreach { case (ex, act) =>
      assert(ex == act)
    }
  }
}
