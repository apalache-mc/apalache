package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTransformations extends FunSuite with TestingPredefs {

  import Builder._

  test("Test Prime") {
    val vars: Set[String] = Set(
        "x",
        "a"
    )
    val transformation = Prime(vars, new IdleTracker())

    val pa1 = n_x -> prime(n_x)
    val pa2 = n_y -> n_y
    val pa3 = prime(n_x) -> prime(n_x)
    val pa4 = and(n_x, n_y, prime(n_a)) -> and(prime(n_x), n_y, prime(n_a))

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
    val pa2 = and(n_x, and(n_y, n_z)) -> and(n_x, n_y, n_z)
    val pa3 = or(n_x, or(n_y, n_z)) -> or(n_x, n_y, n_z)
    val pa4 = or(n_x, and(n_y, n_z)) -> or(n_x, and(n_y, n_z))
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
    ) -> and(
        or(n_a, n_b, n_c, n_d),
        or(n_e, n_f, n_g, NameEx("h"))
    )
    val pa6 = enumSet(or(n_x, and(n_y, n_z))) -> enumSet(or(n_x, and(n_y, n_z)))
    val pa7 = letIn(
        appOp(n_A),
        declOp("A", int(1))
    ) -> letIn(
        appOp(n_A),
        declOp("A", int(1))
    )

    val pa8 = letIn(
        appOp(n_A),
        declOp("A", or(n_x, or(n_y, n_z)))
    ) -> letIn(
        appOp(n_A),
        declOp("A", or(n_x, n_y, n_z))
    )

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
