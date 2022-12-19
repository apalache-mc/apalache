package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.types.tla._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper

import scala.collection.immutable.{SortedMap, SortedSet, TreeMap}

trait TestSymbStateRewriterRecord extends RewriterBase {
  private val ribs = RecT1("a" -> IntT1, "b" -> BoolT1, "c" -> StrT1)
  private val rii = RecT1("a" -> IntT1, "c" -> IntT1)

  test("""RecordDomainCache: ~(dom {"a", "b"} = dom {"a", "b", "c"})""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    val (newArena1, set1) = rewriter.recordDomainCache.create(arena, (SortedSet("a", "b"), SortedSet[String]()))
    val (newArena2, set2) =
      rewriter.recordDomainCache.create(newArena1, (SortedSet("a", "b", "c"), SortedSet[String]()))
    // the domains should not be equal
    val neq = not(eql(set1.toBuilder, set2.toBuilder))
    val state = new SymbState(neq, newArena2, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""["a" |-> 1, "b" |-> FALSE, "c" |-> "d"]""") { rewriterType: SMTEncoding =>
    val record = rec(
        "a" -> int(1),
        "b" -> bool(false),
        "c" -> str("d"),
    )

    val state = new SymbState(record, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case _ @NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case CellTFrom(r @ RecT1(_)) =>
            val map = SortedMap("a" -> IntT1, "b" -> BoolT1, "c" -> StrT1)
            assert(r.fieldTypes == map)
            val keys = SortedSet("a", "b", "c")
            val (_, expectedDomain) =
              rewriter.recordDomainCache.getOrCreate(nextState.arena, (keys, SortedSet[String]()))
            val domain = nextState.arena.getDom(cell)
            assert(rewriter.recordDomainCache.findKey(domain).contains((keys, SortedSet[String]())))
            assert(expectedDomain == domain)

            // also make sure that the domain equality works
            val (newArena, expectedDom) =
              rewriter.recordDomainCache.getOrCreate(nextState.arena, (SortedSet("a", "b", "c"), SortedSet[String]()))
            val eq = eql(expectedDom.toBuilder, dom(cell.toBuilder))
            assertTlaExAndRestore(rewriter, nextState.setArena(newArena).setRex(eq))

          // we check the actual contents in the later tests that access elements

          case _ =>
            fail("Unexpected type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""["a" |-> 1, "b" |-> FALSE, "c" |-> "d"]["c"] equals "d" """) { rewriterType: SMTEncoding =>
    val record = rec(
        "a" -> int(1),
        "b" -> bool(false),
        "c" -> str("d"),
    )
    val recordAcc = app(record, str("b"))
    val eqD = eql(recordAcc, bool(false))

    val state = new SymbState(eqD, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state.setRex(eqD))
  }

  test("""accessing a non-existing field: ["a" |-> 1, "b" |-> FALSE]["c"]""") { rewriterType: SMTEncoding =>
    val record = rec(
        "a" -> int(1),
        "b" -> bool(false),
    ).map { _.withTag(Typed(ribs)) }
    // We assume that record has the type RecT1("a" -> IntT1, "b" -> BoolT1, "c" -> StrT1).
    // This can happen due to type unification. The record access should still work,
    // though the access is expected to produce an arbitrary value (of proper type).
    val recordAcc = app(record, str("c"))

    val state = new SymbState(recordAcc, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""{["a" |-> 1, "b" |-> FALSE], ["a" |-> 2, "b" |-> TRUE]}""") { rewriterType: SMTEncoding =>
    val record1 = rec(
        "a" -> int(1),
        "b" -> bool(false),
    )
    val record2 = rec(
        "a" -> int(2),
        "b" -> bool(true),
    )
    val set = enumSet(record1, record2)
    val state = new SymbState(set, arena, Binding())
    val nextState = create(rewriterType).rewriteUntilDone(state)

    nextState.ex match {
      case NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case CellTFrom(SetT1(rt @ RecT1(_))) =>
            assert(rt.fieldTypes == TreeMap("a" -> IntT1, "b" -> BoolT1))
          // we check the actual contents in the later tests that access elements

          case _ =>
            fail("Unexpected type: " + cell.cellType)
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{["a" |-> 1, "b" |-> FALSE], ["a" |-> 2, "b" |-> TRUE, "c" |-> "foo"]}""") { rewriterType: SMTEncoding =>
    // Although record1 has two fields we provide the type `ribs`. This is how the type checker does type unification.
    val record1 = rec(
        "a" -> int(1),
        "b" -> bool(false),
    ).map { _.withTag(Typed(ribs)) }
    val record2 = rec(
        "a" -> int(2),
        "b" -> bool(true),
        "c" -> str("foo"),
    )
    val recSet = enumSet(record1, record2)
    val state = new SymbState(recSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)

    nextState.ex match {
      case NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case CellTFrom(SetT1(rt @ RecT1(_))) =>
            val map = TreeMap("a" -> IntT1, "b" -> BoolT1, "c" -> StrT1)
            assert(rt.fieldTypes == map)

          case _ =>
            fail("Unexpected type: " + cell.cellType)
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""filter-map a record (idiom): {r.c : r \in {r2 \in {["a" |-> 1], ["a" |-> 2, "c" |-> 3]}: r2.c = 3}}""") {
    rewriterType: SMTEncoding =>
      // It is a common idiom in TLA+ to first filter records by the type field
      // and then -- when knowing the type of the filtered records -- map them somewhere.
      // Although, it is not easy to do in a symbolic encoding, we support this idiom.
      // We require though that all the records have type-compatible fields.
      val record1 = rec("a" -> int(1)).map { _.withTag(Typed(rii)) }
      val record2 = rec("a" -> int(2), "c" -> int(3))
      // Records in a set can have different sets of keys. This requires a type annotation.
      val setEx = enumSet(record1, record2)
      val predEx = eql(app(name("r2", rii), str("c")), int(3))
      val filteredEx = filter(name("r2", rii), setEx, predEx)
      val mapEx = map(
          app(name("r", rii), str("c")),
          name("r", rii) -> filteredEx,
      )

      val eq = eql(mapEx, enumSet(int(3)))

      val state = new SymbState(mapEx, arena, Binding())
      val rewriter = create(rewriterType)
      assertTlaExAndRestore(rewriter, state.setRex(eq))
  }

  test("""[a |-> 1, b |-> FALSE, c |-> "d"] = [c |-> "d", b |-> FALSE, a |-> 1]""") { rewriterType: SMTEncoding =>
    // order of the fields does not matter
    val record1 = rec(
        "a" -> int(1),
        "b" -> bool(false),
        "c" -> str("d"),
    )
    val record2 = rec(
        "c" -> str("d"),
        "b" -> bool(false),
        "a" -> int(1),
    )
    val eq = eql(record1, record2)
    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""~([a |-> 1, b |-> FALSE, c |-> "d"] = [a |-> 1]) equals TRUE""") { rewriterType: SMTEncoding =>
    val record1 = rec(
        "a" -> int(1),
        "b" -> bool(false),
        "c" -> str("d"),
    )
    val record2 = rec("a" -> int(1)).map { _.withTag(Typed(ribs)) }
    val eq = not(eql(record1, record2))
    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""DOMAIN [a |-> 1, b |-> FALSE, c |-> "d"] equals {"a", "b", "c"}""") { rewriterType: SMTEncoding =>
    // the domain of a record stays the same, even if it is lifted to a more general record type
    val record = rec(
        "a" -> int(1),
        "b" -> bool(false),
        "c" -> str("d"),
    )
    val domain = dom(record)
    val eq = eql(domain, enumSet(str("a"), str("b"), str("c")))
    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""DOMAIN [a |-> 1] = {"a"} under type annotations!""") { rewriterType: SMTEncoding =>
    val record = rec("a" -> int(1)).map(_.withTag(Typed(ribs)))
    val domain = dom(record)
    val eq = eql(domain, enumSet(str("a")))
    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""[ ["a" |-> 1, "b" |-> FALSE] EXCEPT !["a"] = 3 ]""") { rewriterType: SMTEncoding =>
    val record = rec(
        "a" -> int(1),
        "b" -> bool(false),
    )
    val updatedRec = except(record, str("a"), int(3)).map {
      // Our rewriting rules expect EXCEPT [<<...>>], but that's type-incorrect w.r.t. the current builder signatures
      // TODO: implement exceptTupled on builder
      case ex @ OperEx(TlaFunOper.except, f, x, e) =>
        OperEx(
            TlaFunOper.except,
            f,
            OperEx(TlaFunOper.tuple, x)(Typed(TupT1(TlaType1.fromTypeTag(x.typeTag)))),
            e,
        )(ex.typeTag)
      case ex => ex
    }
    val expectedRec = rec(
        "a" -> int(3),
        "b" -> bool(false),
    )
    val eq = eql(expectedRec, updatedRec)

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }
}
