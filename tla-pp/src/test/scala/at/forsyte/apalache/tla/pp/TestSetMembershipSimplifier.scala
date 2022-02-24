package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatest.{AppendedClues, BeforeAndAfterEach}
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

/**
 * Tests for SetMembershipSimplifier.
 */
@RunWith(classOf[JUnitRunner])
class TestSetMembershipSimplifier
    extends AnyFunSuite with BeforeAndAfterEach with Checkers with AppendedClues with Matchers {
  private var simplifier: SetMembershipSimplifier = _

  private val tlaTrue = tla.bool(true).as(BoolT1())

  private val boolVal = tla.bool(true).as(BoolT1())
  private val strVal = tla.str("abc").as(StrT1())
  private val intVal = tla.int(42).as(IntT1())

  private val boolName = tla.name("b").as(BoolT1())
  private val strName = tla.name("s").as(StrT1())
  private val intName = tla.name("i").as(IntT1())

  private val boolSet = tla.booleanSet().as(SetT1(BoolT1()))
  private val strSet = tla.stringSet().as(SetT1(StrT1()))
  private val intSet = tla.intSet().as(SetT1(IntT1()))

  private val boolSeqVal = tla.tuple(boolVal, boolName).as(SeqT1(BoolT1()))
  private val strSeqVal = tla.tuple(strVal, strName).as(SeqT1(StrT1()))
  private val intSeqVal = tla.tuple(intVal, intName).as(SeqT1(IntT1()))

  private val boolSeqName = tla.name("boolSeq").as(SeqT1(BoolT1()))
  private val strSeqName = tla.name("strSeq").as(SeqT1(StrT1()))
  private val intSeqName = tla.name("intSeq").as(SeqT1(IntT1()))

  private val boolSeqSet = tla.seqSet(tla.booleanSet()).as(SetT1(SeqT1(BoolT1())))
  private val strSeqSet = tla.seqSet(tla.stringSet()).as(SetT1(SeqT1(StrT1())))
  private val intSeqSet = tla.seqSet(tla.intSet()).as(SetT1(SeqT1(IntT1())))

  val expressions = List(
      (boolName, boolVal, boolSet),
      (strName, strVal, strSet),
      (intName, intVal, intSet),
      (boolSeqName, boolSeqVal, boolSeqSet),
      (strSeqName, strSeqVal, strSeqSet),
      (intSeqName, intSeqVal, intSeqSet),
  )

  override def beforeEach(): Unit = {
    simplifier = SetMembershipSimplifier(new IdleTracker)
  }

  test("simplifies appropriately-typed set membership") {
    expressions.foreach { case (name, value, set) =>
      val inputName = tla.in(name, set).as(BoolT1())
      simplifier(inputName) shouldBe tlaTrue

      val inputValue = tla.in(value, set).as(BoolT1())
      simplifier(inputValue) shouldBe tlaTrue

      val nestedInputName = tla.and(tla.in(name, set).as(BoolT1()), tlaTrue).as(BoolT1())
      simplifier(nestedInputName) shouldBe tla.and(tlaTrue, tlaTrue).as(BoolT1())

      val nestedInputValue = tla.and(tla.in(name, set).as(BoolT1()), tlaTrue).as(BoolT1())
      simplifier(nestedInputValue) shouldBe tla.and(tlaTrue, tlaTrue).as(BoolT1())
    }
  }

  test("returns inappropriately-typed set membership unchanged") {
    expressions.foreach { case (name, value, _) =>
      expressions.filter { case (name2, _, _) => name != name2 }.foreach {
        case (_, _, otherSet) =>
          val inputName = tla.in(name, otherSet).as(BoolT1())
          simplifier(inputName) shouldBe inputName

          val inputValue = tla.in(value, otherSet).as(BoolT1())
          simplifier(inputValue) shouldBe inputValue
      }
    }
  }
}
