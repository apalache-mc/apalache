package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser

trait TestSymbStateRewriterApalache extends RewriterBase with TestingPredefs {
  private val parser = DefaultType1Parser

  private def pair(i: Int, j: Int): TlaEx = tuple(int(i), int(j)).as(parser("<<Int, Int>>"))

  test("""SetAsFun({<<2, 3>>, <<4, 5>>})""") { rewriterType: SMTEncoding =>
    // test that a deterministic relation is translated to a function
    val set = enumSet(pair(2, 3), pair(4, 5)).as(parser("Set(<<Int, Int>>)"))
    val fun = apalacheSetAsFun(set).as(parser("Int -> Int"))

    val state = new SymbState(fun, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val funCell = nextState.asCell

    // the domain should be equal to { 2, 4 }
    val intSet = parser("Set(Int)")
    val domEq = eql(dom(funCell.toNameEx).as(intSet), enumSet(int(2), int(4)).as(intSet)).as(BoolT1)
    assertTlaExAndRestore(rewriter, nextState.setRex(domEq))

    // f[2] = 3
    val app2 = eql(appFun(funCell.toNameEx, int(2)).as(IntT1), int(3)).as(BoolT1)
    assertTlaExAndRestore(rewriter, nextState.setRex(app2))

    // f[4] = 5
    val app4 = eql(appFun(funCell.toNameEx, int(4)).as(IntT1), int(5)).as(BoolT1)
    assertTlaExAndRestore(rewriter, nextState.setRex(app4))
  }

  test("""SetAsFun({<<2, 3>>, <<2, 10>>})""") { rewriterType: SMTEncoding =>
    // Test that a non-deterministic relation is translated to a function.
    // Importantly, consequent calls to int(2) get cached and produce the same cell in the relation.
    // A buggy implementation of DOMAIN was returning a set whose cell simultaneously belonged to the set and not.
    val set = enumSet(pair(2, 3), pair(2, 10)).as(parser("Set(<<Int, Int>>)"))
    val fun = apalacheSetAsFun(set).as(parser("Int -> Int"))

    val state = new SymbState(fun, arena, Binding())
    val rewriter = create(rewriterType)
    var nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val funCell = nextState.asCell

    // probe the cells directly
    val nextArena = nextState.arena
    val relation = nextArena.getCdm(funCell)
    val relationCells = nextArena.getHas(relation)

    def isIn(no: Int): TlaEx = apalacheSelectInSet(relationCells(no).toNameEx, relation.toNameEx).as(BoolT1)

    // These checks cannot be applied to the arrays encoding because it does not have constraints for relation
    if (rewriter.solverContext.config.smtEncoding == SMTEncoding.OOPSLA19) {
      assertTlaExAndRestore(rewriter, nextState.setRex(not(isIn(1)).as(BoolT1)))
      assertTlaExAndRestore(rewriter, nextState.setRex(isIn(0)))
    }

    // f[2] = 3
    val app2 = eql(appFun(fun, int(2)).as(IntT1), int(3)).as(BoolT1)
    assertTlaExAndRestore(rewriter, nextState.setRex(app2))

    // recover the function domain
    val intSet = parser("Set(Int)")
    nextState = rewriter.rewriteUntilDone(nextState.setRex(dom(funCell.toNameEx).as(intSet)))
    val funDom = nextState.asCell
    assert(solverContext.sat())

    // the domain should be equal to { 2 }
    val domEq = eql(funDom.toNameEx.as(intSet), enumSet(int(2)).as(intSet)).as(BoolT1)
    assertTlaExAndRestore(rewriter, nextState.setRex(domEq))
  }

  test("""SetAsFun({})""") { rewriterType: SMTEncoding =>
    // test that an empty set does not break things
    val set = enumSet().as(parser("Set(<<Int, Int>>)"))
    val fun = apalacheSetAsFun(set).as(parser("Int -> Int"))

    val state = new SymbState(fun, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val funCell = nextState.asCell

    // the domain should be equal to { }
    val intSet = parser("Set(Int)")
    val domEq = eql(dom(funCell.toNameEx).as(intSet), enumSet().as(intSet)).as(BoolT1)
    assertTlaExAndRestore(rewriter, nextState.setRex(domEq))
  }
}
