package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.transformations.impl.{IdleTracker, TrackerWithListeners}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.typecheck.{BoolT1, IntT1, OperT1}
import at.forsyte.apalache.tla.typecheck.TypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbTransGenerator extends FunSuite with TestingPredefs {

  val stg = new SymbTransGenerator(TrackerWithListeners())

  import stg.helperFunctions._
  import at.forsyte.apalache.tla.lir.convenience.tla._

  private val types = Map("i" -> IntT1(), "b" -> BoolT1(), "o_b" -> OperT1(Seq(), BoolT1()))

  test("Test allCombinations") {

    assert(allCombinations[Int](Seq.empty[Set[Set[Int]]]).isEmpty)

    val empty = Set.empty[Set[Int]]
    assert(allCombinations(Seq(empty)) == empty)

    val s11 = Set(Set(1))
    val s12 = Set(Set(2))
    val expected1 = Set(Set(1, 2))
    val actual1 = allCombinations[Int](Seq(s11, s12))

    assert(expected1 == actual1)

    val N = 10
    val oneToN = Range(1, N).toSet
    val ss = oneToN.toSeq map { x => Set(Set(x)) }
    val expected2 = Set(oneToN)
    val actual2 = allCombinations[Int](ss)

    assert(expected2 == actual2)

    val s31 = Set(Set(1), Set(2))
    val s32 = Set(Set(3), Set(4))
    val s33 = Set(Set(5), Set(6))
    val expected3 = Set(
        Set(1, 3, 5),
        Set(1, 3, 6),
        Set(1, 4, 5),
        Set(1, 4, 6),
        Set(2, 3, 5),
        Set(2, 3, 6),
        Set(2, 4, 5),
        Set(2, 4, 6)
    )
    val actual3 = allCombinations(Seq(s31, s32, s33))

    assert(actual3 == expected3)
  }

  test("Test labelsAt") {
    val ex11 = tla
      .name("x")
      .typed(IntT1())
    val ex12 = tla
      .name("y")
      .typed(IntT1())
    val ex13 = or(ex11, ex12)
      .typed(BoolT1())

    val sel1: SelMapType = Map(
        ex13.ID -> Set(Set(ex11.ID), Set(ex12.ID))
    )

    val expected1 = Set(ex11.ID, ex12.ID)
    val actual1 = labelsAt(ex13, sel1)

    assert(expected1 == actual1)
  }

  def fromPossiblity(ex: TlaEx, asgn: Set[UID]): (TlaEx, SelMapType, Set[UID]) = {
    val tr = AssignmentOperatorIntroduction(asgn, new IdleTracker)
    val trEx = tr(ex)
    (trEx, allSelections(trEx, Map.empty), asgn map tr.getReplacements)
  }

  test("Test allSelections") {
    val xasgn11 = tla
      .eql(tla.prime(tla.name("x") ? "i") ? "i", tla.name("s") ? "i")
      .typed(types, "b")
    val xasgn12 = tla
      .eql(tla.prime(tla.name("x") ? "i") ? "i", int(1))
      .typed(types, "b")
    val yasgn11 = tla
      .eql(tla.prime(tla.name("x") ? "i") ? "i", tla.name("T") ? "i")
      .typed(types, "b")
    val yasgn12 = tla
      .eql(tla.prime(tla.name("x") ? "i") ? "i", tla.name("t") ? "i")
      .typed(types, "b")

    val ex1 =
      ite(
          ge(int(0), int(1)) ? "b",
          xasgn11,
          xasgn12
      ).typed(types, "b")

    val ex2 = or(yasgn11, yasgn12)
      .typed(types, "b")

    val ex3 = and(
        ex1,
        ex2
    ).typed(types, "b")

    val possibleAssgnsX = Seq(
        Set(xasgn11.ID),
        Set(xasgn12.ID)
    )

    val possibleAssgnsY = Seq(
        Set(yasgn11.ID),
        Set(yasgn12.ID)
    )

    val possibleAssgnsXY = Seq(
        Set(xasgn11.ID, yasgn11.ID),
        Set(xasgn11.ID, yasgn12.ID),
        Set(xasgn12.ID, yasgn11.ID),
        Set(xasgn12.ID, yasgn12.ID)
    )

    val selections1 = possibleAssgnsX map { fromPossiblity(ex1, _) }

    val selections2 = possibleAssgnsY map { fromPossiblity(ex2, _) }

    val selections3 = possibleAssgnsXY map { fromPossiblity(ex3, _) }

    selections1 foreach { case (newEx, s, e) =>
      assert(s(newEx.ID) == Set(e))
    }

    selections2 foreach { case (newEx, s, e) =>
      assert(s(newEx.ID) == Set(e))
    }

    selections3 foreach { case (newEx, s, e) =>
      assert(s(newEx.ID) == Set(e))
    }

    val xasgn21 = tla
      .eql(tla.prime(tla.name("x") ? "i") ? "i", tla.name("x") ? "i")
      .typed(types, "b")
    val yasgn21 = tla
      .eql(tla.prime(tla.name("x") ? "i") ? "i", tla.name("T") ? "i")
      .typed(types, "b")
    val yasgn22 = tla
      .eql(tla.prime(tla.name("y") ? "i") ? "i", tla.name("t") ? "i")
      .typed(types, "b")

    val ex4 = and(eql(int(0), int(1)) ? "b", xasgn21 ? "b")
      .typed(types, "b")
    val xDecl = declOp("X", ex4)
      .typedOperDecl(OperT1(Seq(), BoolT1()))
    val ex5 = and(yasgn21, tla.appOp(tla.name("X") ? "o_b") ? "b")
      .typed(types, "b")
    val ex6 = and(yasgn22, tla.appOp(tla.name("X") ? "o_b") ? "b")
      .typed(types, "b")
    val ex7 = or(ex5, ex6)
      .typed(types, "b")
    val ex8 = letIn(ex7, xDecl)
      .typed(types, "b")

    val possibleAssgnsX2 = Seq(Set(xasgn21.ID))

    val possibleAssgnsXY2 = Seq(
        Set(xasgn21.ID, yasgn21.ID),
        Set(xasgn21.ID, yasgn22.ID)
    )

    val selections4 = possibleAssgnsX2 map {
      fromPossiblity(ex4, _)
    }

    selections4 foreach { case (newEx, s, e) =>
      assert(s(newEx.ID) == Set(e))
    }

    val selections5 = possibleAssgnsXY2 map { fromPossiblity(ex8, _) }

    selections5 foreach { case (newEx, s, e) =>
      // We need to weaken the condition, because LET-IN assignments
      // can appear on any number of branches.
      assert(s(newEx.ID).contains(e))
    }

  }

  test("Test ITE with multibranching") {
    val asgn1 = tla
      .eql(tla.prime(tla.name("x") ? "i") ? "i", int(1))
      .typed(types, "b")
    val asgn2 = tla
      .eql(tla.prime(tla.name("x") ? "i") ? "i", int(2))
      .typed(types, "b")
    val asgn3 = tla
      .eql(tla.prime(tla.name("x") ? "i") ? "i", int(3))
      .typed(types, "b")

    val next = ite(
        tla.bool(true).typed(),
        asgn1,
        ite(
            tla.bool(true).typed(),
            asgn2,
            asgn3
        ) ? "b"
    ).typed(types, "b")

    val sel = Seq(asgn1.ID, asgn2.ID, asgn3.ID)

    val transitions = stg(next, sel)

    // Only expected to work on the above
    def countXprime(ex: TlaEx): Int = ex match {
      case OperEx(TlaActionOper.prime, NameEx("x")) => 1
      case OperEx(_, args @ _*) =>
        (args map countXprime).sum
      case _ => 0
    }

    transitions foreach { t =>
      assert(countXprime(t._2) == 1)
    }

  }

  test("Test LET-IN") {
    val asgn = tla
      .eql(tla.prime(tla.name("x") ? "i") ? "i", int(1))
      .typed(types, "b")
    val xDecl = declOp("X", asgn)
      .typedOperDecl(types, "o_b")
    val disj = or(
        and(tla.name("A") ? "b", tla.appOp(tla.name("X") ? "o_b") ? "b") ? "b",
        and(tla.name("B") ? "b", tla.appOp(tla.name("X") ? "o_b") ? "b") ? "b"
    ).typed(types, "b")

    val next = letIn(
        disj,
        xDecl
    ).typed(types, "b")

    val strat = Seq(asgn.ID)

    val ret = stg(next, strat) map {
      _._2
    }
    assert(ret.size == 1)
    val expected = letIn(disj,
        declOp("X", assign(prime(tla.name("x") ? "i") ? "i", int(1)) ? "b")
          .typedOperDecl(types, "o_b"))
      .typed(types, "b")
    assert(expected == ret.head)
  }

  test("Test sliceWith") {
    val asgn = eql(prime(tla.name("x") ? "i") ? "i", int(1))
      .typed(types, "b")
    val xDecl = declOp("X", asgn)
      .typedOperDecl(types, "o_b")
    val disj = or(
        and(name("A"), appOp(name("X") ? "o_b") ? "b") ? "b",
        and(name("B"), appOp(name("X") ? "o_b") ? "b") ? "b"
    ).typed(types, "b")

    val next = letIn(
        disj,
        xDecl
    ).typed(types, "b")

    val selection = Set(asgn.ID)
    val tr = AssignmentOperatorIntroduction(selection, new IdleTracker)
    val allSelectionsMade = allSelections(tr(next), Map.empty)

    val sliced = sliceWith(selection map tr.getReplacements, allSelectionsMade)(next)

    assert(sliced == next)

  }

}
