package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTransformations extends FunSuite with TestingPredefs {

  import tla._

  test("Test Prime") {
    val vars: Set[String] = Set(
        "x",
        "a"
    )
    val transformation = Prime(vars, new IdleTracker())

    val pa1 = n_x -> prime(n_x).untyped()
    val pa2 = n_y -> n_y
    val pa3 = prime(n_x).untyped() -> prime(n_x).untyped()
    val pa4 = and(n_x, n_y, prime(n_a)).untyped() -> and(prime(n_x), n_y, prime(n_a)).untyped()

    val expected = Seq(
        pa1,
        pa2,
        pa3,
        pa4
    )
    val cmp = expected map { case (k, v) =>
      (v, transformation(k))
    }
    cmp foreach { case (ex, act) =>
      assert(ex == act)
    }
  }

  test("Test Flatten") {
    val transformation = Flatten(new IdleTracker())

    val pa1 = n_x -> n_x
    val pa2 = and(n_x, and(n_y, n_z)).untyped() -> and(n_x, n_y, n_z).untyped()
    val pa3 = or(n_x, or(n_y, n_z)).untyped() -> or(n_x, n_y, n_z).untyped()
    val pa4 = or(n_x, and(n_y, n_z)).untyped() -> or(n_x, and(n_y, n_z)).untyped()
    val pa5 = and(
        and(
            or(
                or(n_a, n_b),
                or(n_c, n_d)
            )
        ),
        and(
            or(
                or(n_e, n_f),
                or(n_g, NameEx("h"))
            )
        )
    ).untyped() -> and(
        or(n_a, n_b, n_c, n_d),
        or(n_e, n_f, n_g, NameEx("h"))
    ).untyped()
    val pa6 = enumSet(or(n_x, and(n_y, n_z))).untyped() -> enumSet(or(n_x, and(n_y, n_z))).untyped()
    val pa7 = letIn(
        appOp(n_A),
        declOp("A", int(1)).untypedOperDecl()
    ).untyped() -> letIn(
        appOp(n_A),
        declOp("A", int(1)).untypedOperDecl()
    ).untyped()

    val pa8 = letIn(
        appOp(n_A),
        declOp("A", or(n_x, or(n_y, n_z))).untypedOperDecl()
    ).untyped() -> letIn(
        appOp(n_A),
        declOp("A", or(n_x, n_y, n_z)).untypedOperDecl()
    ).untyped()

    val expected = Seq(
        pa1,
        pa2,
        pa3,
        pa4,
        pa5,
        pa6,
        pa7,
        pa8
    )
    val cmp = expected map { case (k, v) =>
      (v, transformation(k))
    }
    cmp foreach { case (ex, act) =>
      assert(ex == act)
    }
  }
}
