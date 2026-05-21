package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSkolemizationMarker extends AnyFunSuite with BeforeAndAfterEach {
  private val Int = IntT1
  private val Bool = BoolT1
  private val BoolOper0 = OperT1(Seq(), BoolT1)
  private val IntSet = SetT1(IntT1)

  private var marker = new SkolemizationMarker(TrackerWithListeners())

  override def beforeEach(): Unit = {
    marker = new SkolemizationMarker(TrackerWithListeners())
  }

  test("""mark: \E y \in S: P""") {
    val input = tla.exists(tla.name("y", Int), tla.name("S", IntSet), tla.name("P", Bool)).build
    val expected = tla.skolem(tla.unchecked(input))

    val output = marker(input)
    assert(expected.build == output)
  }

  test("""mark: \E y \in S: P /\ \E z \in S: Q""") {
    val S = tla.name("S", IntSet)
    val left = tla.exists(tla.name("y", Int), S, tla.name("P", Bool)).build
    val right = tla.exists(tla.name("z", Int), S, tla.name("Q", Bool)).build
    val input = tla.and(tla.unchecked(left), tla.unchecked(right)).build
    val expected = tla.and(tla.skolem(tla.unchecked(left)), tla.skolem(tla.unchecked(right)))

    val output = marker(input)
    assert(expected.build == output)
  }

  // see the issue #148
  test("""no mark: x' <- \E y \in S: P""") {
    val input = tla.assign(
        tla.prime(tla.name("x", Bool)),
        tla.exists(tla.name("y", Int), tla.name("S", IntSet), tla.name("P", Bool)),
    ).build

    val output = marker(input)
    assert(input == output)
  }

  // skolemize let-definitions, if they are used positively as part of a formula, see the issue #985
  test("""mark: LET A == \E y \in S: P IN A \/ TRUE""") {
    val bodyOfA = tla.exists(tla.name("y", Int), tla.name("S", IntSet), tla.name("P", Bool))
    val declOfA = tla.decl("A", bodyOfA)
    val A = tla.name("A", BoolOper0)
    val B = tla.bool(true)
    val input = tla.letIn(tla.or(tla.appOp(A), B), declOfA)

    // the body of A is skolemized
    val bodyOfAskolem = tla.skolem(bodyOfA)
    // the skolemized copy of A is used
    val declOfAskolem = tla.decl("A$_skolem", bodyOfAskolem)
    // note that we have two let-in definitions now: one that is skolemized and one that is not skolemized
    val skolemA = tla.name("A$_skolem", BoolOper0)
    val expected =
      LetInEx(tla.or(tla.appOp(skolemA), B).build, declOfA.build, declOfAskolem.build)(Typed(BoolT1))

    val output = marker(input)
    assert(expected.build == output)
  }

  // do not skolemize let-definitions, if they are used as a value, see the issue #985
  test("""mark: LET A == \E y \in S: P IN A = FALSE""") {
    val bodyOfA = tla.exists(tla.name("y", Int), tla.name("S", IntSet), tla.name("P", Bool))
    val declOfA = tla.decl("A", bodyOfA)
    val A = tla.name("A", BoolOper0)
    val B = tla.bool(false)
    val input = tla.letIn(tla.eql(tla.appOp(A), B), declOfA)

    // the body of A is skolemized
    val bodyOfAskolem = tla.skolem(bodyOfA)
    // the skolemized copy of A is used
    val declOfAskolem = tla.decl("A$_skolem", bodyOfAskolem)
    // note that we have two let-in definitions now: one that is skolemized and one that is not skolemized
    val expected =
      LetInEx(tla.eql(tla.appOp(A), B).build, declOfA.build, declOfAskolem.build)(Typed(BoolT1))

    val output = marker(input)
    assert(expected.build == output)
  }

  test("""mark: Cardinality(S) >= 3""") {
    val input = tla.ge(tla.cardinality(tla.name("S", IntSet)), tla.int(3)).build
    val expected = tla.constCard(tla.unchecked(input))
    val output = marker(input)
    assert(expected.build == output)
  }

  test("""no mark: ~(Cardinality(S) >= 3)""") {
    val input = tla.not(tla.ge(tla.cardinality(tla.name("S", IntSet)), tla.int(3))).build
    val output = marker(input)
    assert(input == output)
  }

  test("""no mark: Cardinality(S) < 3""") {
    val input = tla.lt(tla.cardinality(tla.name("S", IntSet)), tla.int(3)).build
    val output = marker(input)
    assert(input == output)
  }
}
