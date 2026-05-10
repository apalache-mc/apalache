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

    val pa1: (TlaEx, TlaEx) = tla.name("x").untyped() -> prime(tla.name("x")).untyped()
    val pa2: (TlaEx, TlaEx) = tla.name("y").untyped() -> tla.name("y").untyped()
    val pa3 = prime(tla.name("x")).untyped() -> prime(tla.name("x")).untyped()
    val pa4 = and(tla.name("x"), tla.name("y"), prime(tla.name("a"))).untyped() -> and(prime(tla.name("x")), tla.name("y"), prime(tla.name("a"))).untyped()

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

    val pa1: (TlaEx, TlaEx) = tla.name("x").untyped() -> tla.name("x").untyped()
    val pa2 = and(tla.name("x"), and(tla.name("y"), tla.name("z"))).untyped() -> and(tla.name("x"), tla.name("y"), tla.name("z")).untyped()
    val pa3 = or(tla.name("x"), or(tla.name("y"), tla.name("z"))).untyped() -> or(tla.name("x"), tla.name("y"), tla.name("z")).untyped()
    val pa4 = or(tla.name("x"), and(tla.name("y"), tla.name("z"))).untyped() -> or(tla.name("x"), and(tla.name("y"), tla.name("z"))).untyped()
    val pa5 = and(
        and(
            or(
                or(tla.name("a"), tla.name("b")),
                or(tla.name("c"), tla.name("d")),
            )
        ),
        and(
            or(
                or(tla.name("e"), tla.name("f")),
                or(tla.name("g"), NameEx("h")),
            )
        ),
    ).untyped() -> and(
        or(tla.name("a"), tla.name("b"), tla.name("c"), tla.name("d")),
        or(tla.name("e"), tla.name("f"), tla.name("g"), NameEx("h")),
    ).untyped()
    val pa6 = enumSet(or(tla.name("x"), and(tla.name("y"), tla.name("z")))).untyped() -> enumSet(or(tla.name("x"), and(tla.name("y"), tla.name("z")))).untyped()
    val pa7 = letIn(
        appOp(tla.name("A")),
        declOp("A", int(1)).untypedOperDecl(),
    ).untyped() -> letIn(
        appOp(tla.name("A")),
        declOp("A", int(1)).untypedOperDecl(),
    ).untyped()

    val pa8 = letIn(
        appOp(tla.name("A")),
        declOp("A", or(tla.name("x"), or(tla.name("y"), tla.name("z")))).untypedOperDecl(),
    ).untyped() -> letIn(
        appOp(tla.name("A")),
        declOp("A", or(tla.name("x"), tla.name("y"), tla.name("z"))).untypedOperDecl(),
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
