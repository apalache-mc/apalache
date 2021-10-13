package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import at.forsyte.apalache.tla.lir.OperParam
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.{keep, touch}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestLetInOptimizer extends FunSuite with BeforeAndAfterEach {

  import at.forsyte.apalache.tla.lir.convenience.tla._

  private var optimizer: LetInOptimizer = _

  private val parser = DefaultType1Parser
  private val intT = parser("Int")
  private val strT = parser("Str")
  private val toStrT = parser("() => Str")

  override def beforeEach(): Unit = {
    optimizer = new LetInOptimizer(new IdleTracker())
  }

  test("""keep values""") {
    val trueValue = bool(true).typed()
    assert(keep(trueValue) == optimizer(touch(trueValue)))
    val intValue = int(42).typed()
    assert(keep(intValue) == optimizer(touch(intValue)))
    val strValue = str("foo").typed()
    assert(keep(strValue) == optimizer(touch(strValue)))
  }

  test("""keep operators without let-in""") {
    val input = plus(int(1), mult(int(2), int(3)) as intT) as intT
    assert(keep(input) == optimizer(touch(input)))
  }

  test("""change 1 unused let-in""") {
    val int1 = int(1).typed()
    // LET Unused == "foo" IN 1
    val input = letIn(int1, declOp("Unused", str("foo")) as toStrT) as intT
    assert(touch(int1) == optimizer(touch(input)))
  }

  test("""keep 1 used let-in""") {
    // LET Used2 == "bar"
    // IN Used2
    // LET Unused == "foo" IN 1
    val used2 = declOp("Used2", str("bar")) as toStrT
    val body = appOp(name("Used2") as toStrT) as strT
    val input = letIn(body, used2) as strT
    assert(keep(input) == optimizer(touch(input)))
  }

  test("""change 1 unused and 1 used let-in""") {
    // LET Unused1 == "foo"
    //     Used2 == "bar"
    // IN Used2
    val unused1 = declOp("Unused1", str("foo")) as toStrT
    val used2 = declOp("Used2", str("bar")) as toStrT
    val body = appOp(name("Used2") as toStrT) as strT
    val input = letIn(body, unused1, used2) as strT
    val expected = letIn(body, used2) as strT
    assert(touch(expected) == optimizer(touch(input)))
  }

  test("""keep lambda let-in""") {
    // Test the special lambda form:
    // SelectSeq(seq, LET f(x) == TRUE IN f)
    val fType = parser("Int => Bool")
    val f = declOp("f", bool(true).typed(), OperParam("x")) as fType
    val seqType = parser("Seq(Int)")
    val input = selectseq(name("seq") as seqType, letIn(name("f") as fType, f) as fType) as seqType
    assert(keep(input) == optimizer(touch(input)))
  }

  test("""change 1 unused let-in in an operator""") {
    val int2 = int(2).typed()
    val int3 = int(3).typed()
    // 2 + (LET Unused == "foo" IN 3)
    val letEx = letIn(int3, declOp("Unused", str("foo")) as toStrT) as intT
    val input = plus(int2, letEx) as intT
    val expected = plus(int2, int3) as intT
    assert(touch(expected) == optimizer(touch(input)))
  }
}
