package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterFun extends RewriterBase {
  private val boolFunT: TlaType1 = FunT1(BoolT1, BoolT1)
  private def intEnum(values: Int*): TBuilderInstruction = tla.enumSet(values.map(i => tla.int(i)): _*)
  private def emptyIntSet: TBuilderInstruction = tla.emptySet(IntT1)
  private def unchecked(ex: TlaEx): TBuilderInstruction = tla.unchecked(ex)

  test("""[x \in {1,2,3,4} |-> x / 3: ]""") { rewriterType: SMTEncoding =>
    val set = intEnum(1, 2, 3, 4)

    val mapping = tla.div(tla.name("x", IntT1), tla.int(3))

    val fun = tla.funDef(mapping, tla.name("x", IntT1) -> set)

    val state = new SymbState(fun, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case CellTFrom(FunT1(IntT1, IntT1)) =>
            () // OK

          case _ =>
            fail("Unexpected type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test(""" [x \in {1,2,3} |-> IF x = 1 THEN {2} ELSE IF x = 2 THEN {3} ELSE {1} ]""") { rewriterType: SMTEncoding =>
    val x = tla.name("x", IntT1)
    val set = intEnum(1, 2, 3)

    def intSet(i: Int) = tla.enumSet(tla.int(i))

    val mapping = tla.ite(
        tla.eql(x, tla.int(1)),
        intSet(2),
        tla.ite(tla.eql(x, tla.int(2)), intSet(3), intSet(1)),
    )
    val fun = tla.funDef(mapping, x -> set)

    val state = new SymbState(fun, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""[x \in {1,2} |-> {} ][1] = {}""") { rewriterType: SMTEncoding =>
    val x = tla.name("x", IntT1)
    val set = tla.enumSet(tla.int(1), tla.int(2))

    val mapping = emptyIntSet

    val fun = tla.funDef(mapping, x -> set)

    val eq = tla.eql(tla.app(fun, tla.int(1)), emptyIntSet)

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(_) =>
        solverContext.push()
        solverContext.assertGroundExpr(result)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(tla.not(unchecked(result)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""[x \in {1,2} |-> IF x = 1 THEN {2} ELSE {1} ][1]""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(tla.int(1), tla.int(2))

    val mapping = tla.ite(tla.eql(tla.name("x", IntT1), tla.int(1)), tla.enumSet(tla.int(2)), tla.enumSet(tla.int(1)))

    val fun = tla.funDef(mapping, tla.name("x", IntT1) -> set)

    val eq = tla.eql(tla.enumSet(tla.int(2)), tla.app(fun, tla.int(1)))

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        assert(solverContext.sat())
        solverContext.push()
        solverContext.assertGroundExpr(nextState.ex)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(tla.not(unchecked(nextState.ex)))
        assert(!solverContext.sat())
        solverContext.pop()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // regression: this test did not work with EWD840
  test("""[x \in {1,2} |-> ["a" |-> x] ][1]""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(tla.int(1), tla.int(2))

    val mapping = tla.rec("a" -> tla.name("x", IntT1))

    val fun = tla.funDef(mapping, tla.name("x", IntT1) -> set)

    val eq = tla.eql(tla.rec("a" -> tla.int(1)), tla.app(fun, tla.int(1)))

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        assert(solverContext.sat())
        solverContext.push()
        solverContext.assertGroundExpr(nextState.ex)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(tla.not(unchecked(nextState.ex)))
        assert(!solverContext.sat())
        solverContext.pop()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""f[4]""") { rewriterType: SMTEncoding =>
    val x = tla.name("x", IntT1)
    val set = intEnum(1, 2, 3, 4)

    val mapping = tla.mult(x, tla.int(3))

    val fun = tla.funDef(mapping, x -> set)

    val app = tla.app(fun, tla.int(4))

    val state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case CellTFrom(IntT1) =>
            val eq1 = tla.eql(cellEx(cell), tla.int(12))

            solverContext.assertGroundExpr(eq1)
            rewriter.push()
            assert(solverContext.sat())
            rewriter.pop()
            val eq2 = tla.neql(cellEx(cell), tla.int(12))

            solverContext.assertGroundExpr(eq2)
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""[x \in {1, 2} |-> x][4] ~~> failure!""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(tla.int(1), tla.int(2))

    val fun = tla.funDef(tla.name("x", IntT1), tla.name("x", IntT1) -> set)
    val app = tla.app(fun, tla.int(4))

    val state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        // In the previous version, we were using failure predicates to detect failures.
        // However, they were an unnecessary burden and produced tonnes of constraints.
        // In the new version, we just return some value,
        // which is similar to Leslie's interpretation.
        // The most important thing is that the SMT context is still satisfiable.
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""[x \in {3} |-> {1, x}][3]""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(tla.int(3))
    val mapping = tla.enumSet(tla.int(1), tla.name("x", IntT1))
    val fun = tla.funDef(mapping, tla.name("x", IntT1) -> set)
    val app = tla.app(fun, tla.int(3))

    val appEq = tla.eql(app, tla.enumSet(tla.int(1), tla.int(3)))

    val state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state.setRex(appEq))
  }

  test("""[x \in {} |-> x][3]""") { rewriterType: SMTEncoding =>
    // regression: function application with an empty domain should not crash.
    // The result of this function is undefined in TLA+.
    val fun = tla.funDef(tla.name("x", IntT1), tla.name("x", IntT1) -> emptyIntSet)
    val app = tla.app(fun, tla.int(3))

    val state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    val _ = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""[y \in BOOLEAN |-> ~y] = [x \in BOOLEAN |-> ~x]""") { rewriterType: SMTEncoding =>
    val fun1 = tla.funDef(tla.not(tla.name("y", BoolT1)), tla.name("y", BoolT1) -> tla.booleanSet())

    val fun2 = tla.funDef(tla.not(tla.name("x", BoolT1)), tla.name("x", BoolT1) -> tla.booleanSet())

    val eq1 = tla.eql(fun1, fun2)

    val state = new SymbState(eq1, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  // a function returning a function
  test("""[x \in {3} |-> [y \in BOOLEAN |-> ~y]][3]""") { rewriterType: SMTEncoding =>
    val boolNegFun = tla.funDef(tla.not(tla.name("y", BoolT1)), tla.name("y", BoolT1) -> tla.booleanSet())

    val fun = tla.funDef(boolNegFun, tla.name("x", IntT1) -> tla.enumSet(tla.int(3)))

    val app = tla.app(fun, tla.int(3))

    val appEq = tla.eql(app, boolNegFun)

    val state = new SymbState(appEq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""[x \in {1, 2} |-> IF x = 1 THEN 11 ELSE 2 * x][1]""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val pred = tla.eql(tla.name("x", IntT1), tla.int(1))
    val ifThenElse = tla.ite(pred, tla.int(11), tla.mult(tla.int(2), tla.name("x", IntT1)))
    val iteFun = tla.funDef(ifThenElse, tla.name("x", IntT1) -> set)
    val iteFunElem = tla.app(iteFun, tla.int(1))
    val iteFunElemNe11 = tla.eql(iteFunElem, tla.int(11))

    val state = new SymbState(iteFunElemNe11, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""[[x \in {1, 2} |-> 2 * x] EXCEPT ![1] = 11]""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val mapExpr = tla.mult(tla.int(2), tla.name("x", IntT1))
    val fun = tla.funDef(mapExpr, tla.name("x", IntT1) -> set)

    val newFun = tla.except(fun, tla.int(1), tla.int(11))

    val state = new SymbState(newFun, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)

    nextState.ex match {
      case NameEx(_) =>
        // check the function domain and co-domain
        val resFun = nextState.asCell
        // check the function co-domain
        val cdm = nextState.arena.getCdm(resFun)
        val cdmSize = nextState.arena.getHas(cdm).size
        assert(cdmSize == 2 || cdmSize == 3) // the co-domain can be overapproximated

      case _ =>
        fail("Unexpected rewriting result")
    }

    val resFun1eq11 = tla.eql(tla.app(newFun, tla.int(1)), tla.int(11))

    assertTlaExAndRestore(rewriter, nextState.setRex(resFun1eq11))
  }

  test("""[[x \in {"a", "b"} |-> 3] EXCEPT !["a"] = 11]""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(tla.str("a"), tla.str("b"))
    val mapExpr = tla.int(3)
    val fun = tla.funDef(mapExpr, tla.name("x", StrT1) -> set)

    val newFun = tla.except(fun, tla.str("a"), tla.int(11))

    val resFun1eq11 = tla.eql(tla.app(newFun, tla.str("a")), tla.int(11))

    val state = new SymbState(newFun, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state.setRex(resFun1eq11))
  }

  test("""fun in a set: \E x \in {[y \in BOOLEAN |-> ~y]}: x[FALSE]""") { rewriterType: SMTEncoding =>
    // this test was failing in the buggy implementation with PICK .. FROM and FUN-MERGE
    val fun1 = tla.funDef(tla.not(tla.name("y", BoolT1)), tla.name("y", BoolT1) -> tla.booleanSet())

    val existsForm =
      tla.skolem(tla.exists(tla.name("x", boolFunT), tla.enumSet(fun1),
              tla.app(tla.name("x", boolFunT), tla.bool(false))))

    val rewriter = createWithoutCache(rewriterType)

    val state = new SymbState(existsForm, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""DOMAIN [x \in {1,2,3} |-> x / 2: ]""") { rewriterType: SMTEncoding =>
    val x = tla.name("x", IntT1)
    val set = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val mapping = tla.div(x, tla.int(2))
    val fun = tla.funDef(mapping, x -> set)
    val domain = tla.dom(fun)
    val eq = tla.eql(domain, set)

    val rewriter = create(rewriterType)
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }
}
