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
 * Tests for [[SetMembershipSimplifier]].
 */
@RunWith(classOf[JUnitRunner])
class TestSetMembershipSimplifier
    extends AnyFunSuite with BeforeAndAfterEach with Checkers with AppendedClues with Matchers {
  private var simplifier: SetMembershipSimplifier = _

  private val tlaTrue = tla.bool(true).as(BoolT1)

  private val boolSeqT: SeqT1 = SeqT1(BoolT1)
  private val strSeqT: SeqT1 = SeqT1(StrT1)
  private val intSeqT: SeqT1 = SeqT1(IntT1)

  private val boolSetT: SetT1 = SetT1(BoolT1)
  private val strSetT: SetT1 = SetT1(StrT1)
  private val intSetT: SetT1 = SetT1(IntT1)

  private val intPowersetSeqType = SeqT1(intSetT)
  private val boolSeqPowersetType = SetT1(boolSeqT)

  private val boolVal = tla.bool(true).as(BoolT1)
  private val strVal = tla.str("abc").as(StrT1)
  private val intVal = tla.int(42).as(IntT1)

  private val boolName = tla.name("b").as(BoolT1)
  private val strName = tla.name("s").as(StrT1)
  private val intName = tla.name("i").as(IntT1)
  private val funName = tla.name("fun").as(FunT1(IntT1, BoolT1))

  private val boolSet = tla.booleanSet().as(boolSetT)
  private val strSet = tla.stringSet().as(strSetT)
  private val intSet = tla.intSet().as(intSetT)

  private val boolSeqVal = tla.tuple(boolVal, boolName).as(boolSeqT)
  private val strSeqVal = tla.tuple(strVal, strName).as(strSeqT)
  private val intSeqVal = tla.tuple(intVal, intName).as(intSeqT)

  private val boolSeqName = tla.name("boolSeq").as(boolSeqT)
  private val strSeqName = tla.name("strSeq").as(strSeqT)
  private val intSeqName = tla.name("intSeq").as(intSeqT)

  private val boolSeqSet = tla.seqSet(tla.booleanSet()).as(SetT1(boolSeqT))
  private val strSeqSet = tla.seqSet(tla.stringSet()).as(SetT1(strSeqT))
  private val intSeqSet = tla.seqSet(tla.intSet()).as(SetT1(intSeqT))
  private val natSeqSet = tla.seqSet(tla.natSet()).as(SetT1(intSeqT))

  private val boolSetVal = tla.enumSet(boolVal, boolName).as(boolSetT)
  private val strSetVal = tla.enumSet(strVal, strName).as(strSetT)
  private val intSetVal = tla.enumSet(intVal, intName).as(intSetT)

  private val boolSetName = tla.name("boolSet").as(boolSetT)
  private val strSetName = tla.name("strSet").as(strSetT)
  private val intSetName = tla.name("intSet").as(intSetT)

  private val boolPowerset = tla.seqSet(tla.booleanSet()).as(SetT1(boolSeqT))
  private val strPowerset = tla.seqSet(tla.stringSet()).as(SetT1(strSeqT))
  private val intPowerset = tla.seqSet(tla.intSet()).as(SetT1(intSeqT))
  private val natPowerset = tla.seqSet(tla.natSet()).as(SetT1(intSeqT))

  private val tupleVal = tla.tuple(tla.int(1).as(IntT1), tla.int(42).as(IntT1)).as(TupT1(IntT1, IntT1))
  private val tupleName = tla.name("tup").as(TupT1(IntT1, IntT1))
  private val cartesianSet =
    tla.times(tla.intSet().as(intSetT), tla.intSet().as(intSetT)).as(SetT1(TupT1(IntT1, IntT1)))

  private val recType = RecT1("a" -> IntT1, "b" -> BoolT1)
  private val recVal = tla.enumFun(tla.str("a").as(StrT1), intVal, tla.str("b").as(StrT1), boolVal).as(recType)
  private val recName = tla.name("rec").as(recType)
  private val recordSet =
    tla.recSet(tla.str("a").as(StrT1), intSet, tla.str("b").as(StrT1), boolSet).as(SetT1(recType))

  override def beforeEach(): Unit = {
    simplifier = SetMembershipSimplifier(new IdleTracker)
  }

  /* *** tests for all supported types of type-defining sets *** */

  test("simplifies type-defining set membership") {
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
        (tupleVal, tupleName, cartesianSet),
        (recVal, recName, recordSet),
    )

    expressions.foreach { case (name, value, set) =>
      // name \in ApplicableSet  ~>  TRUE
      // e.g., b \in BOOLEAN, i \in Int, ...  ~>  TRUE
      val inputName = tla.in(name, set).as(BoolT1)
      simplifier(inputName) shouldBe tlaTrue

      // literal \in ApplicableSet  ~>  TRUE
      // e.g., TRUE \in BOOLEAN, 42 \in Int, ...  ~>  TRUE
      val inputValue = tla.in(value, set).as(BoolT1)
      simplifier(inputValue) shouldBe tlaTrue

      /* *** nested cases *** */

      // name \in ApplicableSet /\ _  ~>  TRUE
      // e.g., i \in Int /\ _, ...  ~>  TRUE
      val nestedInputName = tla.and(tla.in(name, set).as(BoolT1), tlaTrue).as(BoolT1)
      simplifier(nestedInputName) shouldBe tla.and(tlaTrue, tlaTrue).as(BoolT1)

      // literal \in ApplicableSet /\ _  ~>  TRUE
      // e.g., 42 \in Int /\ _, ...  ~>  TRUE
      val nestedInputValue = tla.and(tla.in(name, set).as(BoolT1), tlaTrue).as(BoolT1)
      simplifier(nestedInputValue) shouldBe tla.and(tlaTrue, tlaTrue).as(BoolT1)

      // fun \in [ApplicableSet1 -> ApplicableSet2], ...  ~>  TRUE
      expressions.foreach { case (name2, _, set2) =>
        val funSetType = SetT1(FunT1(name.typeTag.asTlaType1(), name2.typeTag.asTlaType1()))
        val funInFunSet = tla.in(funName, tla.funSet(set, set2).as(funSetType)).as(BoolT1)
        simplifier(funInFunSet) shouldBe tlaTrue
      }
    }
  }

  /* *** tests of particular expressions *** */

  test("rewrites nested Seq/SUBSET to TRUE") {
    // <<{{1}}>> \in Seq(SUBSET Int)  ~>  TRUE
    val setOfSetOfInt = SetT1(intSetT)
    val seqOfSetOfSetOfInt = SeqT1(setOfSetOfInt)
    val nestedSeqSubsetVal =
      tla.tuple(tla.enumSet(intSetVal).as(setOfSetOfInt)).as(SeqT1(setOfSetOfInt)).as(seqOfSetOfSetOfInt)
    val nestedSeqSubsetTest =
      tla.in(nestedSeqSubsetVal, tla.seqSet(tla.powSet(intSet).as(setOfSetOfInt)).as(seqOfSetOfSetOfInt)).as(BoolT1)
    simplifier(nestedSeqSubsetTest) shouldBe tlaTrue

    // {<<1>>} \in SUBSET (Seq(Int))  ~>  TRUE
    val setOfSeqOfInt = SetT1(intSeqT)
    val nestedSubsetSeqVal = tla.enumSet(tla.tuple(intVal).as(intSeqT)).as(setOfSeqOfInt)
    val nestedSubsetSeqTest = tla.in(nestedSubsetSeqVal, tla.powSet(intSeqSet).as(setOfSeqOfInt)).as(BoolT1)
    simplifier(nestedSubsetSeqTest) shouldBe tlaTrue
  }

  test("rewrites function over Seq/SUBSET to TRUE") {
    // fun \in [Seq(SUBSET Int) -> SUBSET Seq(BOOLEAN)], ...  ~>  TRUE
    val nestedFunSetType = SetT1(FunT1(intPowersetSeqType, boolSeqPowersetType))
    val nestedInput = tla
      .in(funName,
          tla
            .funSet(tla.seqSet(intSeqSet).as(intPowersetSeqType), tla.powSet(boolSeqSet).as(boolSeqPowersetType))
            .as(nestedFunSetType))
      .as(BoolT1)
    simplifier(nestedInput) shouldBe tlaTrue
  }

  test("rewrites function over records over Seq/SUBSET to TRUE") {
    import at.forsyte.apalache.tla.lir.convenience.tla._
    // fun \in [["a": Seq(SUBSET Int)] -> ["b": SUBSET Seq(BOOLEAN)]], ...  ~>  TRUE
    val funRecType = SetT1(FunT1(RecT1("a" -> intPowersetSeqType), RecT1("b" -> boolSeqPowersetType)))
    val funRecInput = in(funName,
        funSet(recSet(str("a").as(StrT1), seqSet(intSeqSet).as(intPowersetSeqType))
              .as(RecT1("a" -> intPowersetSeqType)),
            recSet(str("b").as(StrT1), powSet(boolSeqSet).as(boolSeqPowersetType))
              .as(RecT1("b" -> boolSeqPowersetType)))
          .as(funRecType))
      .as(BoolT1)
    simplifier(funRecInput) shouldBe tlaTrue
  }

  test("rewrites non-typedefining function set domain to DOMAIN") {
    // fun \in [RM -> PredefSet], ...  ~>  DOMAIN fun = RM
    val domain = tla.name("RM").as(intSetT)
    val funSetType = SetT1(FunT1(BoolT1, IntT1))
    val funConstToBoolean = tla.in(funName, tla.funSet(domain, boolSet).as(funSetType)).as(BoolT1)
    simplifier(funConstToBoolean) shouldBe tla.eql(tla.dom(funName).as(intSetT), domain).as(BoolT1)
  }

  /* *** rewriting of `Nat` *** */

  test("rewrites i \\in Nat to \\ge") {
    // i \in Nat  ~>  i >= 0
    val intNameInNat = tla.in(intName, tla.natSet()).as(BoolT1)
    val intValInNat = tla.in(intVal, tla.natSet()).as(BoolT1)
    simplifier(intNameInNat) shouldBe tla.ge(intName, tla.int(0)).as(BoolT1)
    simplifier(intValInNat) shouldBe tla.ge(intVal, tla.int(0)).as(BoolT1)
  }

  test("returns myInt \\in Nat unchanged") {
    val intSeqNameInSeqNat = tla.in(intSeqName, natSeqSet).as(BoolT1)
    val intSeqValInSeqNat = tla.in(intSeqVal, natSeqSet).as(BoolT1)
    simplifier(intSeqNameInSeqNat) shouldBe intSeqNameInSeqNat
    simplifier(intSeqValInSeqNat) shouldBe intSeqValInSeqNat

    val intSetNameInNatPowerset = tla.in(intSetName, natPowerset).as(BoolT1)
    val intSetValInNatPowerset = tla.in(intSetVal, natPowerset).as(BoolT1)
    simplifier(intSetNameInNatPowerset) shouldBe intSetNameInNatPowerset
    simplifier(intSetValInNatPowerset) shouldBe intSetValInNatPowerset
  }
}
