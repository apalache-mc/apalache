package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTransformations extends FunSuite with TestingPredefs {

  import Builder._

  private def depthOf(ex: TlaEx): Int = ex match {
    case OperEx(oper, args @ _*) => 1 + (if (args.nonEmpty) (args map depthOf).max else 0)
    case _                       => 1
  }

  test("Test ReplaceFixed") {
    val transformation = ReplaceFixed(n_x, NameEx("y"), new IdleTracker())

    val pa1 = n_x -> n_y
    val pa2 = n_z -> n_z
    val pa3 = prime(n_x) -> prime(n_y)
    val pa4 = ite(n_p, n_x, n_y) -> ite(n_p, n_y, n_y)
    val pa5 = letIn(
        plus(n_z, appOp(n_A)),
        declOp("A", n_q)
    ) -> letIn(
        plus(n_z, appOp(n_A)),
        declOp("A", n_q)
    )
    val pa6 = letIn(
        enumSet(plus(n_x, appOp(n_A)), appOp(n_B, n_x)),
        declOp("A", n_x),
        declOp("B", n_p, "p")
    ) -> letIn(
        enumSet(plus(n_y, appOp(n_A)), appOp(n_B, n_y)),
        declOp("A", n_y),
        declOp("B", n_p, "p")
    )

    val expected = Seq(
        pa1,
        pa2,
        pa3,
        pa4,
        pa5,
        pa6
    )
    val cmp = expected map { case (k, v) =>
      (v, transformation(k))
    }
    cmp foreach { case (ex, act) =>
      assert(ex == act)
    }
  }

  test("Test EqualityAsContainment") {
    val transformation = PrimedEqualityToMembership(new IdleTracker())

    val ex1 = primeEq(n_x, n_y)
    val ex2 = or(primeEq(n_x, n_y), ge(prime(n_x), int(0)))
    val ex3 = ite(primeEq(n_x, n_y), primeEq(n_z, int(0)), primeEq(n_z, int(1)))
    val ex4 = letIn(
        appOp(n_A),
        declOp("A", primeEq(n_x, n_y))
    )

    val expected1 = in(prime(n_x), enumSet(n_y))
    val expected2 = or(in(prime(n_x), enumSet(n_y)), ge(prime(n_x), int(0)))
    val expected3 = ite(
        in(prime(n_x), enumSet(n_y)),
        in(prime(n_z), enumSet(int(0))),
        in(prime(n_z), enumSet(int(1)))
    )
    val expected4 = letIn(
        appOp(n_A),
        declOp("A", in(prime(n_x), enumSet(n_y)))
    )

    val exs = Seq(ex1, ex2, ex3, ex4)
    val expected = Seq(expected1, expected2, expected3, expected4)
    val actual = exs map transformation
    assert(expected == actual)
  }

  test("Test Inline") {
    val cDecl = declOp("C", plus(n_x, int(1)), SimpleFormalParam("x"))
    val operDecls = Seq(
        declOp("A", appOp(n_B)),
        declOp("B", n_c),
        cDecl
    )

    val bodies = BodyMapFactory.makeFromDecls(operDecls)

    val transformation = InlinerOfUserOper(bodies, new IdleTracker())

    val ex1 = n_B
    val ex2 = appOp(n_B)
    val ex3 = n_A
    val ex4 = appOp(n_A)
    val ex5 = or(eql(int(1), int(0)), ge(appDecl(cDecl, appOp(n_A)), int(0)))
    val ex6 = letIn(
        appOp(NameEx("X")),
        declOp("X", appOp(NameEx("C"), n_p))
    )

    val expected1 = n_B // Operators need to be called with apply
    val expected2 = n_c
    val expected3 = n_A // Operators need to be called with apply
    val expected4 = n_c
    val expected5 = or(
        eql(int(1), int(0)),
        ge(plus(n_c, int(1)), int(0))
    )
    val expected6 = letIn(
        appOp(NameEx("X")),
        declOp("X", plus(n_p, int(1)))
    )

    val exs = Seq(ex1, ex2, ex3, ex4, ex5, ex6)
    val expected = Seq(expected1, expected2, expected3, expected4, expected5, expected6)
    val actual = exs map transformation

    assert(expected == actual)

    assertThrows[IllegalArgumentException] {
      transformation(appOp(NameEx("C")))
    }
    assertThrows[IllegalArgumentException] {
      transformation(appOp(NameEx("C"), n_a, n_b))
    }
  }

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
