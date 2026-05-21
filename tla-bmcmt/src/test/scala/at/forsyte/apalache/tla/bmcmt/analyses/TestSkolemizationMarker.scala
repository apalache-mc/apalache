package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{
  ApalacheOper, TlaActionOper, TlaArithOper, TlaBoolOper, TlaFiniteSetOper, TlaOper,
}
import at.forsyte.apalache.tla.lir.values.TlaInt
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
    val input = uExists(uName("y"), uName("S"), uName("P"))
    val expected = uSkolem(input)

    val output = marker(input)
    assert(expected == output)
  }

  test("""mark: \E y \in S: P /\ \E z \in S: Q""") {
    val left = uExists(uName("y"), uName("S"), uName("P"))
    val right = uExists(uName("z"), uName("S"), uName("Q"))
    val input = uAnd(left, right)
    val expected = uAnd(uSkolem(left), uSkolem(right))

    val output = marker(input)
    assert(expected == output)
  }

  // see the issue #148
  test("""no mark: x' <- \E y \in S: P""") {
    val input =
      uAssign(uPrime(uName("x")), uExists(uName("y"), uName("S"), uName("P")))

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
    val input = uGe(uCard(uName("S")), uInt(3))
    val expected = uConstCard(input)
    val output = marker(input)
    assert(expected == output)
  }

  test("""no mark: ~(Cardinality(S) >= 3)""") {
    val input = uNot(uGe(uCard(uName("S")), uInt(3)))
    val output = marker(input)
    assert(input == output)
  }

  test("""no mark: Cardinality(S) < 3""") {
    val input = uLt(uCard(uName("S")), uInt(3))
    val output = marker(input)
    assert(input == output)
  }

  private def uName(name: String): TlaEx = NameEx(name)(Untyped)
  private def uInt(value: Int): TlaEx = ValEx(TlaInt(value))(Untyped)
  private def uOp(oper: TlaOper, args: TlaEx*): TlaEx = OperEx(oper, args: _*)(Untyped)
  private def uExists(name: TlaEx, set: TlaEx, pred: TlaEx): TlaEx = uOp(TlaBoolOper.exists, name, set, pred)
  private def uAnd(args: TlaEx*): TlaEx = uOp(TlaBoolOper.and, args: _*)
  private def uNot(arg: TlaEx): TlaEx = uOp(TlaBoolOper.not, arg)
  private def uGe(left: TlaEx, right: TlaEx): TlaEx = uOp(TlaArithOper.ge, left, right)
  private def uLt(left: TlaEx, right: TlaEx): TlaEx = uOp(TlaArithOper.lt, left, right)
  private def uCard(set: TlaEx): TlaEx = uOp(TlaFiniteSetOper.cardinality, set)
  private def uPrime(ex: TlaEx): TlaEx = uOp(TlaActionOper.prime, ex)
  private def uAssign(left: TlaEx, right: TlaEx): TlaEx = uOp(ApalacheOper.assign, left, right)
  private def uSkolem(ex: TlaEx): TlaEx = uOp(ApalacheOper.skolem, ex)
  private def uConstCard(ex: TlaEx): TlaEx = uOp(ApalacheOper.constCard, ex)
}
