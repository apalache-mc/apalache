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
    val rewriter = create()
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
    val rewriter = create()
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
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case BoolT() =>
            assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(cell.toNameEx, tla.bool(false))))

            // we check the actual contents in the later tests that access elements

          case _ =>
            fail("Expected Boolean type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""type inference error ["a" |-> 1, "b" |-> FALSE]["c"]""") {
    val record = tla.enumFun(tla.str("a"), tla.int(1), tla.str("b"), tla.bool(false))

    val recordAcc = tla.appFun(record, tla.str("c"))
    val state = new SymbState(recordAcc, CellTheory(), arena, new Binding)
    val rewriter = create()
    assertThrows[TypeInferenceError] {
      rewriter.rewriteUntilDone(state)
    }
  }

  test("""SE-REC-CTOR[1-2] in a set: {["a" |-> 1, "b" |-> FALSE], ["a" |-> 2, "b" |-> TRUE]} ~~> $C$k""") {
    val record1 = tla.enumFun(tla.str("a"), tla.int(1), tla.str("b"), tla.bool(false))
    val record2 = tla.enumFun(tla.str("a"), tla.int(2), tla.str("b"), tla.bool(true))

    val state = new SymbState(tla.enumSet(record1, record2), CellTheory(), arena, new Binding)
    val nextState = create().rewriteUntilDone(state)
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
    val record1 = tla.enumFun(tla.str("a"), tla.int(1),
      tla.str("b"), tla.bool(false))
    val record2 = tla.enumFun(tla.str("a"), tla.int(2),
      tla.str("b"), tla.bool(true), tla.str("c"), tla.int(3))
    // Records in a set can have different sets of keys. This requires a type annotation.
    val annotation = AnnotationParser.toTla(RecordT(SortedMap("a" -> IntT(), "b" -> BoolT(), "c" -> IntT())))

    val state = new SymbState(tla.enumSet(tla.withType(record1, annotation), record2), CellTheory(), arena, new Binding)
    val rewriter = create()
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
    // this is a badly-typed expression
    assertThrows[TypeInferenceError] {
      create().rewriteUntilDone(state)
    }
  }

  test("""filter-map a record (idiom): {r.c : r \in {r2 \in {["a" |-> 1], ["a" |-> 2, "c" |-> 3]}: r2.c = 3}} ~~> $C$k""") {
    // It is a common idiom in TLA+ to first filter records by the type field
    // and then -- when knowing the type of the filtered records -- map them somewhere.
    // Although, it is not easy to do in a symbolic encoding, we support this idiom.
    // We require though that all the records should have type-compatible fields.
    val record1 = tla.enumFun(tla.str("a"), tla.int(1))
    val record2 = tla.enumFun(tla.str("a"), tla.int(2), tla.str("c"), tla.int(3))
    // Records in a set can have different sets of keys. This requires a type annotation.
    val annotation = AnnotationParser.toTla(RecordT(SortedMap("a" -> IntT(), "c" -> IntT())))
    val setEx = tla.enumSet(tla.withType(record1, annotation), record2)
    val predEx = tla.eql(tla.appFun(tla.name("r2"), tla.str("c")), tla.int(3))
    val filteredEx = tla.filter(tla.name("r2"), setEx, predEx)
    val mapEx = tla.map(tla.appFun(tla.name("r"), tla.str("c")), tla.name("r"), filteredEx)

    val state = new SymbState(mapEx, CellTheory(), arena, new Binding)
    val rewriter = create()
    rewriter.push()
    val nextState = rewriter.rewriteUntilDone(state)
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(nextState.ex, tla.enumSet(tla.int(3)))))
    rewriter.pop()
    rewriter.push()
    val filteredState = rewriter.rewriteUntilDone(state.setRex(filteredEx))
    val cell = nextState.arena.findCellByNameEx(filteredState.ex)
    assert(cell.cellType == FinSetT(RecordT(SortedMap("a" -> IntT(), "c" -> IntT()))))
  }

  test("""SE-REC-EQ: [a |-> 1, b |-> FALSE, c |-> "d"] = [c |-> "d", b |-> FALSE, a |-> 1] ~~> TRUE""") {
    val record1 = tla.enumFun(tla.str("a"), tla.int(1),
      tla.str("b"), tla.bool(false), tla.str("c"), tla.str("d"))
    val record2 = tla.enumFun(tla.str("c"), tla.str("d"),
      tla.str("b"), tla.bool(false), tla.str("a"), tla.int(1))
    val eq = tla.eql(record1, record2)
    val state = new SymbState(eq, CellTheory(), arena, new Binding)
    val rewriter = create()
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-REC-EQ: [a |-> 1, b |-> FALSE, c |-> "d"] /= [a |-> 1] ~~> TRUE""") {
    // Introduce two different records using a type annotation. The records should not be equal!
    val annotation = AnnotationParser.toTla(RecordT(SortedMap("a" -> IntT(), "b" -> BoolT(), "c" -> ConstT())))

    val record1 = tla.enumFun(tla.str("a"), tla.int(1),
      tla.str("b"), tla.bool(false), tla.str("c"), tla.str("d"))
    val record2 = tla.enumFun(tla.str("a"), tla.int(1))
    val eq = tla.neql(record1, tla.withType(record2, annotation))
    val state = new SymbState(eq, CellTheory(), arena, new Binding)
    val rewriter = create()
    assertTlaExAndRestore(rewriter, state)
  }

}
