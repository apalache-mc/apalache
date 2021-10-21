package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, OperT1, SetT1}
import at.forsyte.apalache.tla.lir.TypedPredefs.{BuilderExAsTyped, BuilderOperDeclAsTyped}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestSkolemizationMarker extends FunSuite with BeforeAndAfterEach {

  import at.forsyte.apalache.tla.lir.convenience.tla._

  private val Int = IntT1()
  private val Bool = BoolT1()
  private val BoolOper0 = OperT1(Seq(), BoolT1())
  private val IntSet = SetT1(IntT1())

  private var marker = new SkolemizationMarker(TrackerWithListeners())

  override def beforeEach(): Unit = {
    marker = new SkolemizationMarker(TrackerWithListeners())
  }

  test("""mark: \E y \in S: P""") {
    val input = exists(name("y"), name("S"), name("P")).untyped()
    val expected = apalacheSkolem(input).untyped()

    val output = marker(input)
    assert(expected == output)
  }

  test("""mark: \E y \in S: P /\ \E z \in S: Q""") {
    val left = exists(name("y"), name("S"), name("P"))
    val right = exists(name("z"), name("S"), name("Q"))
    val input = and(left, right).untyped()
    val expected = and(apalacheSkolem(left), apalacheSkolem(right)).untyped()

    val output = marker(input)
    assert(expected == output)
  }

  // see the issue #148
  test("""no mark: x' <- \E y \in S: P""") {
    val input =
      assignPrime(name("x"), exists(name("y"), name("S"), name("P"))).untyped()

    val output = marker(input)
    assert(input == output)
  }

  // skolemize let-definitions, if they are used positively as part of a formula, see the issue #985
  test("""mark: LET A == \E y \in S: P IN A \/ TRUE""") {
    val bodyOfA = exists(name("y") as Int, name("S") as IntSet, name("P") as Bool) as Bool
    val declOfA = declOp("A", bodyOfA) as BoolOper0
    val A = name("A") as BoolOper0
    val B = bool(true).typed()
    val input = letIn(or(appOp(A) as Bool, B) as Bool, declOfA) as Bool

    // the body of A is skolemized
    val bodyOfAskolem = apalacheSkolem(bodyOfA) as Bool
    // the skolemized copy of A is used
    val declOfAskolem = declOp("A$_skolem", bodyOfAskolem) as BoolOper0
    // note that we have two let-in definitions now: one that is skolemized and one that is not skolemized
    val skolemA = name("A$_skolem") as BoolOper0
    val expected = letIn(or(appOp(skolemA) as Bool, B) as Bool, declOfA, declOfAskolem) as Bool

    val output = marker(input)
    assert(expected == output)
  }

  // do not skolemize let-definitions, if they are used as a value, see the issue #985
  test("""mark: LET A == \E y \in S: P IN A = FALSE""") {
    val bodyOfA = exists(name("y") as Int, name("S") as IntSet, name("P") as Bool) as Bool
    val declOfA = declOp("A", bodyOfA) as BoolOper0
    val A = name("A") as BoolOper0
    val B = bool(false).typed()
    val input = letIn(eql(appOp(A) as Bool, B) as Bool, declOfA) as Bool

    // the body of A is skolemized
    val bodyOfAskolem = apalacheSkolem(bodyOfA) as Bool
    // the skolemized copy of A is used
    val declOfAskolem = declOp("A$_skolem", bodyOfAskolem) as BoolOper0
    // note that we have two let-in definitions now: one that is skolemized and one that is not skolemized
    val expected = letIn(eql(appOp(A) as Bool, B) as Bool, declOfA, declOfAskolem) as Bool

    val output = marker(input)
    assert(expected == output)
  }

  test("""mark: Cardinality(S) >= 3""") {
    val input = ge(card(name("S")), int(3)).untyped()
    val expected = apalacheConstCard(input).untyped()
    val output = marker(input)
    assert(expected == output)
  }

  test("""no mark: ~(Cardinality(S) >= 3)""") {
    val input = not(ge(card(name("S")), int(3))).untyped()
    val output = marker(input)
    assert(input == output)
  }

  test("""no mark: Cardinality(S) < 3""") {
    val input = lt(card(name("S")), int(3)).untyped()
    val output = marker(input)
    assert(input == output)
  }

}
