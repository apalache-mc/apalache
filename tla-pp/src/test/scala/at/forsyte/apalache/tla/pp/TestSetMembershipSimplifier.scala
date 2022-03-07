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
  private val funName = tla.name("fun").as(FunT1(IntT1(), BoolT1()))

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
  private val natSeqSet = tla.seqSet(tla.natSet()).as(SetT1(SeqT1(IntT1())))

  private val boolSetVal = tla.enumSet(boolVal, boolName).as(SetT1(BoolT1()))
  private val strSetVal = tla.enumSet(strVal, strName).as(SetT1(StrT1()))
  private val intSetVal = tla.enumSet(intVal, intName).as(SetT1(IntT1()))

  private val boolSetName = tla.name("boolSet").as(SetT1(BoolT1()))
  private val strSetName = tla.name("strSet").as(SetT1(StrT1()))
  private val intSetName = tla.name("intSet").as(SetT1(IntT1()))

  private val boolPowerset = tla.seqSet(tla.booleanSet()).as(SetT1(SeqT1(BoolT1())))
  private val strPowerset = tla.seqSet(tla.stringSet()).as(SetT1(SeqT1(StrT1())))
  private val intPowerset = tla.seqSet(tla.intSet()).as(SetT1(SeqT1(IntT1())))
  private val natPowerset = tla.seqSet(tla.natSet()).as(SetT1(SeqT1(IntT1())))

  val expressions = List(
      (boolName, boolVal, boolSet),
      (strName, strVal, strSet),
      (intName, intVal, intSet),
      (boolSeqName, boolSeqVal, boolSeqSet),
      (strSeqName, strSeqVal, strSeqSet),
      (intSeqName, intSeqVal, intSeqSet),
      (boolSetName, boolSetVal, boolPowerset),
      (strSetName, strSetVal, strPowerset),
      (intSetName, intSetVal, intPowerset),
  )

  override def beforeEach(): Unit = {
    simplifier = SetMembershipSimplifier(new IdleTracker)
  }

  test("simplifies appropriately-typed set membership") {
    // i \in Nat  ~>  i >= 0
    val intNameInNat = tla.in(intName, tla.natSet()).as(BoolT1())
    val intValInNat = tla.in(intVal, tla.natSet()).as(BoolT1())
    simplifier(intNameInNat) shouldBe tla.ge(intName, tla.int(0)).as(BoolT1())
    simplifier(intValInNat) shouldBe tla.ge(intVal, tla.int(0)).as(BoolT1())

    /* *** tests for all supported types of applicable sets *** */

    expressions.foreach { case (name, value, set) =>
      // name \in ApplicableSet  ~>  TRUE
      // e.g., b \in BOOLEAN, i \in Int, ...  ~>  TRUE
      val inputName = tla.in(name, set).as(BoolT1())
      simplifier(inputName) shouldBe tlaTrue

      // literal \in ApplicableSet  ~>  TRUE
      // e.g., TRUE \in BOOLEAN, 42 \in Int, ...  ~>  TRUE
      val inputValue = tla.in(value, set).as(BoolT1())
      simplifier(inputValue) shouldBe tlaTrue

      /* *** nested cases *** */

      // name \in ApplicableSet /\ _  ~>  TRUE
      // e.g., i \in Int /\ _, ...  ~>  TRUE
      val nestedInputName = tla.and(tla.in(name, set).as(BoolT1()), tlaTrue).as(BoolT1())
      simplifier(nestedInputName) shouldBe tla.and(tlaTrue, tlaTrue).as(BoolT1())

      // literal \in ApplicableSet /\ _  ~>  TRUE
      // e.g., 42 \in Int /\ _, ...  ~>  TRUE
      val nestedInputValue = tla.and(tla.in(name, set).as(BoolT1()), tlaTrue).as(BoolT1())
      simplifier(nestedInputValue) shouldBe tla.and(tlaTrue, tlaTrue).as(BoolT1())

      // fun \in [ApplicableSet1 -> ApplicableSet2], ...  ~>  TRUE
      expressions.foreach { case (name2, _, set2) =>
        val funSetType = SetT1(FunT1(name.typeTag.asTlaType1(), name2.typeTag.asTlaType1()))
        val funInFunSet = tla.in(funName, tla.funSet(set, set2).as(funSetType)).as(BoolT1())
        simplifier(funInFunSet) shouldBe tlaTrue
      }
    }

    /* *** tests of particular expressions *** */

    // <<{{1}}>> \in Seq(SUBSET Int)  ~>  TRUE
    val setOfSetOfInt = SetT1(SetT1(IntT1()))
    val seqOfSetOfSetOfInt = SeqT1(setOfSetOfInt)
    val nestedSeqSubsetVal =
      tla.tuple(tla.enumSet(intSetVal).as(setOfSetOfInt)).as(SeqT1(setOfSetOfInt)).as(seqOfSetOfSetOfInt)
    val nestedSeqSubsetTest =
      tla.in(nestedSeqSubsetVal, tla.seqSet(tla.powSet(intSet).as(setOfSetOfInt)).as(seqOfSetOfSetOfInt)).as(BoolT1())
    simplifier(nestedSeqSubsetTest) shouldBe tlaTrue

    // {<<1>>} \in SUBSET (Seq(Int))  ~>  TRUE
    val setOfSeqOfInt = SetT1(SeqT1(IntT1()))
    val nestedSubsetSeqVal = tla.enumSet(tla.tuple(intVal).as(SeqT1(IntT1()))).as(setOfSeqOfInt)
    val nestedSubsetSeqTest = tla.in(nestedSubsetSeqVal, tla.powSet(intSeqSet).as(setOfSeqOfInt)).as(BoolT1())
    simplifier(nestedSubsetSeqTest) shouldBe tlaTrue

    // fun \in [Seq(SUBSET Int) -> SUBSET Seq(BOOLEAN)], ...  ~>  TRUE
    val intPowersetSeqType = SeqT1(SetT1(IntT1()))
    val boolSeqPowersetType = SetT1(SeqT1(BoolT1()))
    val nestedFunSetType = SetT1(FunT1(intPowersetSeqType, boolSeqPowersetType))
    val nestedInput = tla
      .in(funName,
          tla
            .funSet(tla.seqSet(intSeqSet).as(intPowersetSeqType), tla.powSet(boolSeqSet).as(boolSeqPowersetType))
            .as(nestedFunSetType))
      .as(BoolT1())
    simplifier(nestedInput) shouldBe tlaTrue

    // fun \in [RM -> PredefSet], ...  ~>  DOMAIN fun = RM
    val domain = tla.name("RM").as(SetT1(IntT1()))
    val funSetType = SetT1(FunT1(BoolT1(), IntT1()))
    val funConstToBoolean = tla.in(funName, tla.funSet(domain, boolSet).as(funSetType)).as(BoolT1())
    simplifier(funConstToBoolean) shouldBe tla.eql(tla.dom(funName).as(SetT1(IntT1())), domain).as(BoolT1())
  }

  test("returns myInt \\in Nat unchanged") {
    val intSeqNameInSeqNat = tla.in(intSeqName, natSeqSet).as(BoolT1())
    val intSeqValInSeqNat = tla.in(intSeqVal, natSeqSet).as(BoolT1())
    simplifier(intSeqNameInSeqNat) shouldBe intSeqNameInSeqNat
    simplifier(intSeqValInSeqNat) shouldBe intSeqValInSeqNat

    val intSetNameInNatPowerset = tla.in(intSetName, natPowerset).as(BoolT1())
    val intSetValInNatPowerset = tla.in(intSetVal, natPowerset).as(BoolT1())
    simplifier(intSetNameInNatPowerset) shouldBe intSetNameInNatPowerset
    simplifier(intSetValInNatPowerset) shouldBe intSetValInNatPowerset
  }
}
