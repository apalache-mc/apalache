package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.TypedPredefs._

trait TestSymbStateRewriterFun extends RewriterBase with TestingPredefs {
  private val types =
    Map("b" -> BoolT1(), "B" -> SetT1(BoolT1()), "i" -> IntT1(), "I" -> SetT1(IntT1()), "(i)" -> TupT1(IntT1()),
        "i_to_i" -> FunT1(IntT1(), IntT1()), "i_to_I" -> FunT1(IntT1(), SetT1(IntT1())), "r" -> RecT1("a" -> IntT1()),
        "s" -> StrT1(), "S" -> SetT1(StrT1()), "(s)" -> TupT1(StrT1()), "i_to_s" -> FunT1(StrT1(), IntT1()),
        "s_to_i" -> FunT1(IntT1(), StrT1()), "i_to_r" -> FunT1(IntT1(), RecT1("a" -> IntT1())),
        "b_to_b" -> FunT1(BoolT1(), BoolT1()), "b_TO_b" -> SetT1(FunT1(BoolT1(), BoolT1())),
        "i_to_b_to_b" -> FunT1(IntT1(), FunT1(BoolT1(), BoolT1())))

  test("""[x \in {1,2,3,4} |-> x / 3: ]""") { rewriterType: String =>
    val set = enumSet(1.to(4).map(int): _*)
      .typed(types, "I")
    val mapping = div(name("x") ? "i", int(3))
      .typed(types, "i")
    val fun = funDef(mapping, name("x") ? "i", set)
      .typed(types, "i_to_i")

    val state = new SymbState(fun, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case FunT(FinSetT(IntT()), IntT()) =>
            () // OK

          case _ =>
            fail("Unexpected type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test(""" [x \in {1,2,3} |-> IF x = 1 THEN {2} ELSE IF x = 2 THEN {3} ELSE {1} ]""") { rewriterType: String =>
    val set = enumSet(1.to(3).map(int): _*)
      .typed(types, "I")

    def intSet(i: Int) = enumSet(int(i)).typed(types, "I")

    val mapping = ite(
        eql(name("x"), int(1)) ? "b",
        intSet(2),
        ite(eql(name("x") ? "i", int(2)) ? "b", intSet(3), intSet(1)) ? "I"
    ).typed(types, "I")
    val fun = funDef(mapping, name("x") ? "i", set)
      .typed(types, "i_to_I")

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

  test("""[x \in {1,2} |-> {} ][1] = {}""") { rewriterType: String =>
    val set = enumSet(int(1), int(2))
      .typed(types, "I")
    val mapping = enumSet()
      .typed(types, "I")
    val fun = funDef(mapping, name("x"), set)
      .typed(types, "i_to_I")
    val eq = eql(appFun(fun, int(1)) ? "I", enumSet() ? "I")
      .typed(types, "b")

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
        solverContext.assertGroundExpr(not(result ? "b").typed(types, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""[x \in {1,2} |-> IF x = 1 THEN {2} ELSE {1} ][1]""") { rewriterType: String =>
    val set = enumSet(int(1), int(2))
      .typed(types, "I")
    val mapping = ite(eql(name("x") ? "i", int(1)) ? "b", enumSet(int(2)) ? "I", enumSet(int(1)) ? "I")
      .typed(types, "I")
    val fun = funDef(mapping, name("x") ? "i", set)
      .typed(types, "i_to_I")
    val eq = eql(enumSet(int(2)) ? "I", appFun(fun, int(1)) ? "I")
      .typed(types, "b")

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
        solverContext.assertGroundExpr(not(nextState.ex ? "b").typed(types, "b"))
        assert(!solverContext.sat())
        solverContext.pop()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // regression: this test did not work with EWD840
  test("""[x \in {1,2} |-> ["a" |-> x] ][1]""") { rewriterType: String =>
    val set = enumSet(int(1), int(2))
      .typed(types, "I")
    val mapping = enumFun(str("a"), name("x") ? "i")
      .typed(types, "r")
    val fun = funDef(mapping, name("x") ? "i", set)
      .typed(types, "i_to_r")
    val eq = eql(enumFun(str("a"), int(1)) ? "r", appFun(fun, int(1)) ? "r")
      .typed(types, "b")

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
        solverContext.assertGroundExpr(not(nextState.ex ? "b").typed(types, "b"))
        assert(!solverContext.sat())
        solverContext.pop()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""f[4]""") { rewriterType: String =>
    val set = enumSet(1.to(4).map(int): _*)
      .typed(types, "I")
    val mapping = mult(name("x"), int(3))
      .typed(types, "i")
    val fun = funDef(mapping, name("x"), set)
      .typed(types, "i_to_i")
    val app = appFun(fun, int(4))
      .typed(types, "i")

    val state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case IntT() =>
            val eq1 = eql(cell.toNameEx ? "i", int(12))
              .typed(types, "b")
            solverContext.assertGroundExpr(eq1)
            rewriter.push()
            assert(solverContext.sat())
            rewriter.pop()
            val eq2 = neql(cell.toNameEx ? "i", int(12))
              .typed(types, "b")
            solverContext.assertGroundExpr(eq2)
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""[x \in {1, 2} |-> x][4] ~~> failure!""") { rewriterType: String =>
    val set = enumSet(int(1), int(2))
      .typed(types, "I")
    val fun = funDef(name("x") ? "i", name("x") ? "i", set)
    val app = appFun(fun ? "i_to_i", int(4))
      .typed(types, "i")

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

  // Raft is directly using f @@ e :> r to construct a function g such as:
  // DOMAIN g = {e} \cup DOMAIN f and g[e] = r and g[a] = f[a] for a \in DOMAIN f
  // It is trivial to implement this extension with our encoding
  test("""[x \in {1, 2} |-> x] @@ 3 :> 4""") { rewriterType: String =>
    val set = enumSet(int(1), int(2))
    val fun = funDef(name("x") ? "i", name("x") ? "i", set ? "I")
    val extFun = atat(fun ? "i_to_i", colonGreater(int(3), int(4)) ? "i_to_i")
      .typed(types, "i_to_i")

    val rewriter = create(rewriterType)
    val extState = rewriter.rewriteUntilDone(new SymbState(extFun, arena, Binding()))
    assert(solverContext.sat())
    val eq1 = eql(int(4), appFun(extFun, int(3)) ? "i")
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, extState.setRex(eq1))
  }

  test("""[x \in {3} |-> {1, x}][3]""") { rewriterType: String =>
    val set = enumSet(int(3))
    val mapping = enumSet(int(1), name("x") ? "i")
    val fun = funDef(mapping ? "I", name("x") ? "i", set ? "I")
    val app = appFun(fun ? "i_to_I", int(3))
      .typed(types, "I")

    val appEq = eql(app, enumSet(int(1), int(3)) ? "I")
      .typed(types, "b")
    val state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state.setRex(appEq))
  }

  test("""[x \in {} |-> x][3]""") { rewriterType: String =>
    // regression: function application with an empty domain should not crash.
    // The result of this function is undefined in TLA+.
    val fun = funDef(name("x") ? "i", name("x") ? "i", enumSet() ? "I")
    val app = appFun(fun ? "i_to_i", int(3))
      .typed(types, "i")
    val state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    val _ = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""[y \in BOOLEAN |-> ~y] = [x \in BOOLEAN |-> ~x]""") { rewriterType: String =>
    val fun1 = funDef(not(name("y") ? "b") ? "b", name("y") ? "b", booleanSet() ? "B")
      .typed(types, "b_to_b")
    val fun2 = funDef(not(name("x") ? "b") ? "b", name("x") ? "b", booleanSet() ? "B")
      .typed(types, "b_to_b")
    val eq1 = eql(fun1, fun2)
      .typed(types, "b")

    val state = new SymbState(eq1, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  // a function returning a function
  test("""[x \in {3} |-> [y \in BOOLEAN |-> ~y]][3]""") { rewriterType: String =>
    val boolNegFun = funDef(not(name("y") ? "b") ? "b", name("y") ? "b", booleanSet() ? "B")
      .typed(types, "b_to_b")

    val fun = funDef(boolNegFun, name("x") ? "i", enumSet(int(3)) ? "I")
      .typed(types, "i_to_b_to_b")
    val app = appFun(fun, int(3))
      .typed(types, "b_to_b")

    val appEq = eql(app, boolNegFun)
      .typed(BoolT1())

    val state = new SymbState(appEq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""[x \in {1, 2} |-> IF x = 1 THEN 11 ELSE 2 * x][1]""") { rewriterType: String =>
    val set = enumSet(int(1), int(2))
    val pred = eql(name("x") ? "i", int(1))
    val ifThenElse = ite(pred ? "b", int(11), mult(int(2), name("x") ? "i") ? "i")
    val iteFun = funDef(ifThenElse ? "i", name("x") ? "i", set ? "I")
    val iteFunElem = appFun(iteFun ? "i_to_i", int(1))
    val iteFunElemNe11 = eql(iteFunElem ? "i", int(11))
      .typed(types, "b")

    val state = new SymbState(iteFunElemNe11, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""[[x \in {1, 2} |-> 2 * x] EXCEPT ![1] = 11]""") { rewriterType: String =>
    val set = enumSet(int(1), int(2))
    val mapExpr = mult(int(2), name("x") ? "i")
    val fun = funDef(mapExpr ? "i", name("x") ? "i", set ? "I")
      .typed(types, "i_to_i")

    val newFun = except(fun, tuple(int(1)) ? "(i)", int(11))
      .typed(types, "i_to_i")

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

    val resFun1eq11 = eql(appFun(newFun, int(1)) ? "i", int(11))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(resFun1eq11))
  }

  test("""[[x \in {"a", "b"} |-> 3] EXCEPT !["a"] = 11]""") { rewriterType: String =>
    val set = enumSet(str("a"), str("b"))
    val mapExpr = int(3)
    val fun = funDef(mapExpr ? "i", name("x") ? "s", set ? "S")
      .typed(types, "s_to_i")
    val newFun = except(fun, tuple(str("a")) ? "(s)", int(11))
      .typed(types, "s_to_i")
    val resFun1eq11 = eql(appFun(newFun, str("a")) ? "i", int(11))
      .typed(types, "b")

    val state = new SymbState(newFun, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state.setRex(resFun1eq11))
  }

  test("""fun in a set: \E x \in {[y \in BOOLEAN |-> ~y]}: x[FALSE]""") { rewriterType: String =>
    // this test was failing in the buggy implementation with PICK .. FROM and FUN-MERGE
    val fun1 = funDef(not(name("y") ? "b") ? "b", name("y") ? "b", booleanSet() ? "B")
      .typed(types, "b_to_b")
    val existsForm =
      apalacheSkolem(exists(name("x") ? "b_to_b", enumSet(fun1) ? "b_TO_b",
              appFun(name("x") ? "b_to_b", bool(false)) ? "b") ? "b")
        .typed(types, "b")

    val rewriter = createWithoutCache(rewriterType)

    val state = new SymbState(existsForm, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""DOMAIN [x \in {1,2,3} |-> x / 2: ]""") { rewriterType: String =>
    val set = enumSet(int(1), int(2), int(3))
    val mapping = div(name("x"), int(2))
    val fun = funDef(mapping ? "i", name("x") ? "i", set ? "I")
    val domain = dom(fun ? "i_to_i")
    val eq = eql(domain ? "I", set ? "I")
      .typed(types, "b")

    val rewriter = create(rewriterType)
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }
}
