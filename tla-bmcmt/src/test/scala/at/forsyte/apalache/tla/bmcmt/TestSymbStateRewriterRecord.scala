package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{BoolT, ConstT, FinSetT, IntT, RecordT}
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, NameEx, RecT1, SetT1, StrT1, TupT1}
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.{SortedMap, SortedSet, TreeMap}

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterRecord extends RewriterBase {
  private val types = Map(
      "b" -> BoolT1(),
      "i" -> IntT1(),
      "I" -> SetT1(IntT1()),
      "s" -> StrT1(),
      "(s)" -> TupT1(StrT1()),
      "S" -> SetT1(StrT1()),
      "rib" -> RecT1("a" -> IntT1(), "b" -> BoolT1()),
      "RIB" -> SetT1(RecT1("a" -> IntT1(), "b" -> BoolT1())),
      "ribs" -> RecT1("a" -> IntT1(), "b" -> BoolT1(), "c" -> StrT1()),
      "RIBS" -> SetT1(RecT1("a" -> IntT1(), "b" -> BoolT1(), "c" -> StrT1())),
      "rib" -> RecT1("a" -> IntT1(), "b" -> BoolT1()),
      "rii" -> RecT1("a" -> IntT1(), "c" -> IntT1()),
      "RII" -> SetT1(RecT1("a" -> IntT1(), "c" -> IntT1()))
  )

  test("""RecordDomainCache: ~(dom {"a", "b"} = dom {"a", "b", "c"})""") { rewriter: SymbStateRewriter =>
    val (newArena1, set1) = rewriter.recordDomainCache.create(arena, (SortedSet("a", "b"), SortedSet[String]()))
    val (newArena2, set2) =
      rewriter.recordDomainCache.create(newArena1, (SortedSet("a", "b", "c"), SortedSet[String]()))
    // the domains should not be equal
    val neq = not(eql(set1.toNameEx, set2.toNameEx) ? "b")
      .typed(types, "b")
    val state = new SymbState(neq, newArena2, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""["a" |-> 1, "b" |-> FALSE, "c" |-> "d"]""") { rewriter: SymbStateRewriter =>
    val record = enumFun(str("a"), int(1), str("b"), bool(false), str("c"), str("d"))
      .typed(types, "ribs")

    val state = new SymbState(record, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case _ @NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case r @ RecordT(_) =>
            assert(r.fields == SortedMap("a" -> IntT(), "b" -> BoolT(), "c" -> ConstT()))
            val keys = SortedSet("a", "b", "c")
            val (_, expectedDomain) =
              rewriter.recordDomainCache.getOrCreate(nextState.arena, (keys, SortedSet[String]()))
            val domain = nextState.arena.getDom(cell)
            assert(rewriter.recordDomainCache.findKey(domain).contains((keys, SortedSet[String]())))
            assert(expectedDomain == domain)

            // also make sure that the domain equality works
            val (newArena, expectedDom) =
              rewriter.recordDomainCache.getOrCreate(nextState.arena, (SortedSet("a", "b", "c"), SortedSet[String]()))
            val eq = eql(expectedDom.toNameEx ? "S", dom(cell.toNameEx) ? "S")
              .typed(types, "b")
            assertTlaExAndRestore(rewriter, nextState.setArena(newArena).setRex(eq))

          // we check the actual contents in the later tests that access elements

          case _ =>
            fail("Unexpected type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""["a" |-> 1, "b" |-> FALSE, "c" |-> "d"]["c"] equals "d" """) { rewriter: SymbStateRewriter =>
    val record = enumFun(str("a"), int(1), str("b"), bool(false), str("c"), str("d"))
    val recordAcc = appFun(record ? "ribs", str("b") ? "s")
    val eqD = eql(recordAcc ? "b", bool(false))
      .typed(types, "b")

    val state = new SymbState(eqD, arena, Binding())
    assertTlaExAndRestore(rewriter, state.setRex(eqD))
  }

  test("""accessing a non-existing field: ["a" |-> 1, "b" |-> FALSE]["c"]""") { rewriter: SymbStateRewriter =>
    val record = enumFun(str("a"), int(1), str("b"), bool(false))
    // We assume that record has the type RecT1("a" -> IntT1(), "b" -> BoolT1(), "c" -> StrT1()).
    // This can happen due to type unification. The record access should still work,
    // though the access is expected to produce an arbitrary value (of proper type).
    val recordAcc = appFun(record ? "ribs", str("c"))
      .typed(types, "s")

    val state = new SymbState(recordAcc, arena, Binding())
    rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""{["a" |-> 1, "b" |-> FALSE], ["a" |-> 2, "b" |-> TRUE]}""") { rewriter: SymbStateRewriter =>
    val record1 = enumFun(str("a"), int(1), str("b"), bool(false))
    val record2 = enumFun(str("a"), int(2), str("b"), bool(true))
    val set = enumSet(record1 ? "rib", record2 ? "rib")
      .typed(types, "RIB")
    val state = new SymbState(set, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)

    nextState.ex match {
      case NameEx(name) =>
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

  test("""{["a" |-> 1, "b" |-> FALSE], ["a" |-> 2, "b" |-> TRUE, "c" |-> "foo"]}""") { rewriter: SymbStateRewriter =>
    // Although record1 has two fields we provide the type `ribs`. This is how the type checker does type unification.
    val record1 = enumFun(str("a"), int(1), str("b"), bool(false))
      .typed(types, "ribs")
    val record2 = enumFun(str("a"), int(2), str("b"), bool(true), str("c"), str("foo"))
      .typed(types, "ribs")
    val recSet = enumSet(record1, record2)
      .typed(types, "RIBS")
    val state = new SymbState(recSet, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)

    nextState.ex match {
      case NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case FinSetT(rt @ RecordT(_)) =>
            assert(rt.fields == TreeMap("a" -> IntT(), "b" -> BoolT(), "c" -> ConstT()))

          case _ =>
            fail("Unexpected type: " + cell.cellType)
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""filter-map a record (idiom): {r.c : r \in {r2 \in {["a" |-> 1], ["a" |-> 2, "c" |-> 3]}: r2.c = 3}}""") {
    rewriter: SymbStateRewriter =>
      // It is a common idiom in TLA+ to first filter records by the type field
      // and then -- when knowing the type of the filtered records -- map them somewhere.
      // Although, it is not easy to do in a symbolic encoding, we support this idiom.
      // We require though that all the records have type-compatible fields.
      val record1 = enumFun(str("a"), int(1))
        .typed(types, "rii")
      val record2 = enumFun(str("a"), int(2), str("c"), int(3))
        .typed(types, "rii")
      // Records in a set can have different sets of keys. This requires a type annotation.
      val setEx = enumSet(record1, record2)
        .typed(types, "RII")
      val predEx = eql(appFun(name("r2") ? "rii", str("c")) ? "i", int(3))
        .typed(types, "b")
      val filteredEx = filter(name("r2") ? "rii", setEx, predEx)
        .typed(types, "RII")
      val mapEx = map(appFun(name("r") ? "rii", str("c")) ? "i", name("r") ? "rii", filteredEx)
        .typed(types, "I")

      val eq = eql(mapEx, enumSet(int(3)) ? "I")
        .typed(types, "b")

      val state = new SymbState(mapEx, arena, Binding())
      assertTlaExAndRestore(rewriter, state.setRex(eq))
  }

  test("""[a |-> 1, b |-> FALSE, c |-> "d"] = [c |-> "d", b |-> FALSE, a |-> 1]""") { rewriter: SymbStateRewriter =>
    // order of the fields does not matter
    val record1 = enumFun(str("a"), int(1), str("b"), bool(false), str("c"), str("d"))
    val record2 = enumFun(str("c"), str("d"), str("b"), bool(false), str("a"), int(1))
    val eq = eql(record1 ? "ribs", record2 ? "ribs")
      .typed(types, "b")
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""~([a |-> 1, b |-> FALSE, c |-> "d"] = [a |-> 1]) equals TRUE""") { rewriter: SymbStateRewriter =>
    val record1 = enumFun(str("a"), int(1), str("b"), bool(false), str("c"), str("d"))
    val record2 = enumFun(str("a"), int(1))
    val eq = not(eql(record1 ? "ribs", record2 ? "ribs") ? "b")
      .typed(types, "b")
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""DOMAIN [a |-> 1, b |-> FALSE, c |-> "d"] equals {"a", "b", "c"}""") { rewriter: SymbStateRewriter =>
    // the domain of a record stays the same, even if it is lifted to a more general record type
    val record = enumFun(str("a"), int(1), str("b"), bool(false), str("c"), str("d"))
    val domain = dom(record ? "ribs")
    val eq = eql(domain ? "S", enumSet(str("a"), str("b"), str("c")) ? "S")
      .typed(types, "b")
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""DOMAIN [a |-> 1] = {"a"} under type annotations!""") { rewriter: SymbStateRewriter =>
    val record = enumFun(str("a"), int(1))
      .typed(types, "ribs")
    val domain = dom(record)
    val eq = eql(domain ? "S", enumSet(str("a")) ? "S")
      .typed(types, "b")
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""[ ["a" |-> 1, "b" |-> FALSE] EXCEPT !["a"] = 3 ]""") { rewriter: SymbStateRewriter =>
    val record = enumFun(str("a"), int(1), str("b"), bool(false))
    val updatedRec = except(record ? "rib", tuple(str("a")) ? "(s)", int(3))
      .typed(types, "rib")
    val expectedRec = enumFun(str("a"), int(3), str("b"), bool(false))
      .typed(types, "rib")
    val eq = eql(expectedRec, updatedRec)
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }
}
