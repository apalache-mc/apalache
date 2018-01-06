package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.{SortedMap, SortedSet, TreeMap}

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterRecord extends RewriterBase {
  test("""RecordDomainCache: dom {"a", "b"} /= dom {"a", "b", "c"} ~~> $C$k""") {
    val rewriter = new SymbStateRewriter(solverContext)
    val (newArena1, set1) = rewriter.recordDomainCache.create(arena, SortedSet("a", "b"))
    val (newArena2, set2) = rewriter.recordDomainCache.create(newArena1, SortedSet("a", "b", "c"))
    val neq = tla.not(tla.eql(set1, set2))
    val state = new SymbState(neq, CellTheory(), newArena2, new Binding)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-REC-CTOR[1-2]: ["a" |-> 1, "b" |-> FALSE, "c" |-> "d"] ~~> $C$k""") {
    val record = tla.enumFun(tla.str("a"), tla.int(1),
      tla.str("b"), tla.bool(false), tla.str("c"), tla.str("d"))

    val state = new SymbState(record, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case r @ RecordT(_) =>
            assert(r.fields == SortedMap("a" -> IntT(), "b" -> BoolT(), "c" -> ConstT()))
            val keys = SortedSet("a", "b", "c")
            val (_, expectedDomain) = rewriter.recordDomainCache.getOrCreate(nextState.arena, keys)
            val domain = nextState.arena.getDom(cell)
            assert(rewriter.recordDomainCache.findKey(domain).contains(keys))
            assert(expectedDomain == domain)

            // also make sure that the domain equality works
            val (newArena, expectedDom) =
              rewriter.recordDomainCache.getOrCreate(nextState.arena, SortedSet("a", "b", "c"))
            val eq = tla.eql(expectedDom.toNameEx, tla.dom(cell.toNameEx))
            assertTlaExAndRestore(rewriter, nextState.setArena(newArena).setRex(eq))

            // we check the actual contents in the later tests that access elements

          case _ =>
            fail("Unexpected type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-REC-ACC[1-2]: ["a" |-> 1, "b" |-> FALSE, "c" |-> "d"]["c"] ~~> $C$k equals \"d\"""") {
    val record = tla.enumFun(tla.str("a"), tla.int(1),
      tla.str("b"), tla.bool(false), tla.str("c"), tla.str("d"))

    val recordAcc = tla.appFun(record, tla.str("b"))
    val state = new SymbState(recordAcc, CellTheory(), arena, new Binding)
    val nextState = new SymbStateRewriter(solverContext).rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case BoolT() =>
            assert(solverContext.sat())
            solverContext.push()
            solverContext.assertGroundExpr(tla.eql(cell.toNameEx, tla.bool(false)))
            assert(solverContext.sat())
            solverContext.pop()
            solverContext.assertGroundExpr(tla.eql(cell.toNameEx, tla.bool(true)))
            assert(!solverContext.sat())

            // we check the actual contents in the later tests that access elements

          case _ =>
            fail("Expected Boolean type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-REC-CTOR[1-2] in a set: {["a" |-> 1, "b" |-> FALSE], ["a" |-> 2, "b" |-> TRUE]} ~~> $C$k""") {
    val record1 = tla.enumFun(tla.str("a"), tla.int(1), tla.str("b"), tla.bool(false))
    val record2 = tla.enumFun(tla.str("a"), tla.int(2), tla.str("b"), tla.bool(true))

    val state = new SymbState(tla.enumSet(record1, record2), CellTheory(), arena, new Binding)
    val nextState = new SymbStateRewriter(solverContext).rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case FinSetT(rt @ RecordT(_)) =>
            assert(rt.fields == TreeMap("a" -> IntT(), "b" -> BoolT()))

          // we check the actual contents in the later tests that access elements

          case _ =>
            fail("Unexpected type: " + cell.cellType)
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-REC-CTOR[1-2] in a set: {["a" |-> 1, "b" |-> FALSE], ["a" |-> 2, "b" |-> TRUE, "c" |-> 3]} ~~> $C$k""") {
    // records in a set can have different -- although compatible -- sets of keys
    val record1 = tla.enumFun(tla.str("a"), tla.int(1),
      tla.str("b"), tla.bool(false))
    val record2 = tla.enumFun(tla.str("a"), tla.int(2),
      tla.str("b"), tla.bool(true), tla.str("c"), tla.int(3))

    val state = new SymbState(tla.enumSet(record1, record2), CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case FinSetT(rt @ RecordT(_)) =>
            assert(rt.fields == TreeMap("a" -> IntT(), "b" -> BoolT(), "c" -> IntT()))


          case _ =>
            fail("Unexpected type: " + cell.cellType)
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-REC-CTOR[1-2] type error: {["a" |-> FALSE, "b" |-> 1], ["a" |-> 2, "b" |-> TRUE]} ~~> $C$k""") {
    val record1 = tla.enumFun(tla.str("a"), tla.bool(false), tla.str("b"), tla.int(1))
    val record2 = tla.enumFun(tla.str("a"), tla.int(2), tla.str("b"), tla.bool(true))

    val state = new SymbState(tla.enumSet(record1, record2), CellTheory(), arena, new Binding)
    try {
      new SymbStateRewriter(solverContext).rewriteUntilDone(state)
      fail("Expected a type error")
    } catch {
      case _: TypeException =>
        () // OK
    }
  }

}
