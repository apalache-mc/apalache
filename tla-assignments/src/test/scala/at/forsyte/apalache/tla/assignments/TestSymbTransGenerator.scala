package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.transformations.impl.{IdleTracker, TrackerWithListeners}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import TypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import scala.collection.immutable.{SortedMap, SortedSet}

@RunWith(classOf[JUnitRunner])
class TestSymbTransGenerator extends AnyFunSuite with TestingPredefs {

  val stg = new SymbTransGenerator(TrackerWithListeners())

  import stg.helperFunctions._
  import at.forsyte.apalache.tla.lir.convenience.tla._

  private val Int = IntT1
  private val Bool = BoolT1
  private val ToBool = OperT1(Seq(), BoolT1)

  test("Test allCombinations") {

    assert(allCombinations(Seq[AssignmentSelections]()).isEmpty)

    val empty = Set[SortedSet[UID]]()
    assert(allCombinations(Seq(empty)) == empty)

    val N = 10
    val uids = Range(1, N).map(_ => UID.unique).toList
    val s11 = Set(SortedSet(uids(1)))
    val s12 = Set(SortedSet(uids(2)))
    val expected1 = Set(SortedSet(uids(1), uids(2)))
    val actual1 = allCombinations(Seq(s11, s12))

    assert(expected1 == actual1)

    val oneToN = Range(1, N).map(_ => UID.unique).to(SortedSet)
    val ss = oneToN.toSeq.map { x => Set(SortedSet(x)) }
    val expected2 = Set(oneToN)
    val actual2 = allCombinations(ss)

    assert(expected2 == actual2)

    val s31 = Set(SortedSet(uids(1)), SortedSet(uids(2)))
    val s32 = Set(SortedSet(uids(3)), SortedSet(uids(4)))
    val s33 = Set(SortedSet(uids(5)), SortedSet(uids(6)))
    val expected3 = Set(
        SortedSet(uids(1), uids(3), uids(5)),
        SortedSet(uids(1), uids(3), uids(6)),
        SortedSet(uids(1), uids(4), uids(5)),
        SortedSet(uids(1), uids(4), uids(6)),
        SortedSet(uids(2), uids(3), uids(5)),
        SortedSet(uids(2), uids(3), uids(6)),
        SortedSet(uids(2), uids(4), uids(5)),
        SortedSet(uids(2), uids(4), uids(6)),
    )
    val actual3 = allCombinations(Seq(s31, s32, s33))

    assert(actual3 == expected3)
  }

  test("Test labelsAt") {
    val ex11 = tla
      .name("x")
      .typed(IntT1)
    val ex12 = tla
      .name("y")
      .typed(IntT1)
    val ex13 = or(ex11, ex12)
      .typed(BoolT1)

    val sel1: SelMapType = SortedMap(
        ex13.ID -> Set(SortedSet(ex11.ID), SortedSet(ex12.ID))
    )

    val expected1 = Set(ex11.ID, ex12.ID)
    val actual1 = labelsAt(ex13, sel1)

    assert(expected1 == actual1)
  }

  def fromPossiblity(ex: TlaEx, asgn: SortedSet[UID]): (TlaEx, SelMapType, SortedSet[UID]) = {
    val tr = AssignmentOperatorIntroduction(asgn, new IdleTracker)
    val trEx = tr(ex)
    (trEx, allSelections(trEx, SortedMap.empty), asgn.map(tr.getReplacements))
  }

  test("Test allSelections") {
    val xasgn11 = tla.eql(tla.prime(tla.name("x").as(Int)).as(Int), tla.name("s").as(Int)).as(Bool)
    val xasgn12 = tla.eql(tla.prime(tla.name("x").as(Int)).as(Int), int(1)).as(Bool)
    val yasgn11 = tla.eql(tla.prime(tla.name("x").as(Int)).as(Int), tla.name("T").as(Int)).as(Bool)
    val yasgn12 = tla.eql(tla.prime(tla.name("x").as(Int)).as(Int), tla.name("t").as(Int)).as(Bool)

    val ex1 =
      ite(
          ge(int(0), int(1)).as(Bool),
          xasgn11,
          xasgn12,
      ).as(Bool)

    val ex2 = or(yasgn11, yasgn12).as(Bool)

    val ex3 = and(ex1, ex2).as(Bool)

    val possibleAssgnsX = Seq(SortedSet(xasgn11.ID), SortedSet(xasgn12.ID))

    val possibleAssgnsY = Seq(SortedSet(yasgn11.ID), SortedSet(yasgn12.ID))

    val possibleAssgnsXY = Seq(
        SortedSet(xasgn11.ID, yasgn11.ID),
        SortedSet(xasgn11.ID, yasgn12.ID),
        SortedSet(xasgn12.ID, yasgn11.ID),
        SortedSet(xasgn12.ID, yasgn12.ID),
    )

    val selections1 = possibleAssgnsX.map { fromPossiblity(ex1, _) }

    val selections2 = possibleAssgnsY.map { fromPossiblity(ex2, _) }

    val selections3 = possibleAssgnsXY.map { fromPossiblity(ex3, _) }

    selections1.foreach { case (newEx, s, e) =>
      assert(s(newEx.ID) == Set(e))
    }

    selections2.foreach { case (newEx, s, e) =>
      assert(s(newEx.ID) == Set(e))
    }

    selections3.foreach { case (newEx, s, e) =>
      assert(s(newEx.ID) == Set(e))
    }

    val xasgn21 = tla.eql(tla.prime(tla.name("x").as(Int)).as(Int), tla.name("x").as(Int)).as(Bool)
    val yasgn21 = tla.eql(tla.prime(tla.name("x").as(Int)).as(Int), tla.name("T").as(Int)).as(Bool)
    val yasgn22 = tla.eql(tla.prime(tla.name("y").as(Int)).as(Int), tla.name("t").as(Int)).as(Bool)

    val ex4 = and(eql(int(0), int(1)).as(Bool), xasgn21).as(Bool)
    val xDecl = declOp("X", ex4).as(OperT1(Seq(), BoolT1))
    val ex5 = and(yasgn21, tla.appOp(tla.name("X").as(ToBool)).as(Bool)).as(Bool)
    val ex6 = and(yasgn22, tla.appOp(tla.name("X").as(ToBool)).as(Bool)).as(Bool)
    val ex7 = or(ex5, ex6).as(Bool)
    val ex8 = letIn(ex7, xDecl).as(Bool)

    val possibleAssgnsX2 = Seq(SortedSet(xasgn21.ID))

    val possibleAssgnsXY2 = Seq(
        SortedSet(xasgn21.ID, yasgn21.ID),
        SortedSet(xasgn21.ID, yasgn22.ID),
    )

    val selections4 = possibleAssgnsX2.map {
      fromPossiblity(ex4, _)
    }

    selections4.foreach { case (newEx, s, e) =>
      assert(s(newEx.ID) == Set(e))
    }

    val selections5 = possibleAssgnsXY2.map { fromPossiblity(ex8, _) }

    selections5.foreach { case (newEx, s, e) =>
      // We need to weaken the condition, because LET-IN assignments
      // can appear on any number of branches.
      assert(s(newEx.ID).contains(e))
    }

  }

  test("Test ITE with multibranching") {
    val asgn1 = tla.eql(tla.prime(tla.name("x").as(Int)).as(Int), int(1)).as(Bool)
    val asgn2 = tla.eql(tla.prime(tla.name("x").as(Int)).as(Int), int(2)).as(Bool)
    val asgn3 = tla.eql(tla.prime(tla.name("x").as(Int)).as(Int), int(3)).as(Bool)

    val next = ite(
        tla.bool(true).typed(),
        asgn1,
        ite(
            tla.bool(true).typed(),
            asgn2,
            asgn3,
        ).as(Bool),
    ).as(Bool)

    val sel = Seq(asgn1.ID, asgn2.ID, asgn3.ID)

    val transitions = stg(next, sel)

    // Only expected to work on the above
    def countXprime(ex: TlaEx): Int = ex match {
      case OperEx(TlaActionOper.prime, NameEx("x")) => 1
      case OperEx(_, args @ _*)                     =>
        (args.map(countXprime)).sum
      case _ => 0
    }

    transitions.foreach { t =>
      assert(countXprime(t._2) == 1)
    }

  }

  test("Test LET-IN") {
    val asgn = tla.eql(tla.prime(tla.name("x").as(Int)).as(Int), int(1)).as(Bool)
    val xDecl = declOp("X", asgn).as(ToBool)
    val disj = or(
        and(tla.name("A").as(Bool), tla.appOp(tla.name("X").as(ToBool)).as(Bool)).as(Bool),
        and(tla.name("B").as(Bool), tla.appOp(tla.name("X").as(ToBool)).as(Bool)).as(Bool),
    ).as(Bool)

    val next = letIn(disj, xDecl).as(Bool)

    val strat = Seq(asgn.ID)

    val ret = stg(next, strat).map {
      _._2
    }
    assert(ret.size == 1)
    val declOfX =
      declOp("X", assign(prime(tla.name("x").as(Int)).as(Int), int(1)).as(Bool)).as(ToBool)
    val expected = letIn(disj, declOfX)
      .as(Bool)
    assert(expected == ret.head)
  }

  test("Test sliceWith") {
    val asgn = eql(prime(tla.name("x").as(Int)).as(Int), int(1)).as(Bool)
    val xDecl = declOp("X", asgn).as(ToBool)
    val disj = or(
        and(name("A"), appOp(name("X").as(ToBool)).as(Bool)).as(Bool),
        and(name("B"), appOp(name("X").as(ToBool)).as(Bool)).as(Bool),
    ).as(Bool)

    val next = letIn(disj, xDecl).as(Bool)

    val selection = Set(asgn.ID)
    val tr = AssignmentOperatorIntroduction(selection, new IdleTracker)
    val allSelectionsMade = allSelections(tr(next), SortedMap.empty)

    val sliced = sliceWith(selection.map(tr.getReplacements), allSelectionsMade)(next)

    assert(sliced == next)

  }

  test("Disjunction with labels") {
    // \/ (L1: x' = 1)
    val equality1 = eql(prime(name("x").as(Int)).as(Int), int(1)).as(Bool)
    val labelledEquality1 = label(equality1, "L1").as(Bool)
    //  \/ (L2: x' = 2)
    val equality2 = eql(prime(name("x").as(Int)).as(Int), int(2)).as(Bool)
    val labelledEquality2 = label(equality2, "L2").as(Bool)
    // next == (L1: x' = 1) \/ (L2: x' = 2)
    val next = or(labelledEquality1, labelledEquality2).as(Bool)
    // select only the first assignment
    val selections = Seq(equality1.ID, equality2.ID)
    val transitions = stg(next, selections)
    assert(transitions.size == 2)
    // the equalities are transformed into assignments
    // \/ (L1:: x' := 1)
    // \/ (L2:: x' := 2)
    val assign1 = label(assign(prime(name("x")).as(Int), int(1)).as(Bool), "L1").as(Bool)
    val assign2 = label(assign(prime(name("x")).as(Int), int(2)).as(Bool), "L2").as(Bool)
    assert(transitions.head._2 == assign1)
    assert(transitions(1)._2 == assign2)
  }
}
