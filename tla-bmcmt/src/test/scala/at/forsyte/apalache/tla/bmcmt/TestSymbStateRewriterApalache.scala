package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterApalache extends RewriterBase {
  private val parser = DefaultType1Parser

  private def pair(i: Int, j: Int): TBuilderInstruction = tla.tuple(tla.int(i), tla.int(j))

  test("""SetAsFun({<<2, 3>>, <<4, 5>>})""") { rewriterType: SMTEncoding =>
    // test that a deterministic relation is translated to a function
    val set = tla.enumSet(pair(2, 3), pair(4, 5))
    val fun = tla.setAsFun(set)

    val state = new SymbState(fun, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val funCell = nextState.asCell

    // the domain should be equal to { 2, 4 }
    val domEq = tla.eql(tla.dom(tla.unchecked(funCell.toNameEx)), tla.enumSet(tla.int(2), tla.int(4)))
    assertTlaExAndRestore(rewriter, nextState.setRex(domEq))

    // f[2] = 3
    val app2 = tla.eql(tla.app(tla.unchecked(funCell.toNameEx), tla.int(2)), tla.int(3))
    assertTlaExAndRestore(rewriter, nextState.setRex(app2))

    // f[4] = 5
    val app4 = tla.eql(tla.app(tla.unchecked(funCell.toNameEx), tla.int(4)), tla.int(5))
    assertTlaExAndRestore(rewriter, nextState.setRex(app4))
  }

  test("""SetAsFun({<<2, 3>>, <<2, 10>>})""") { rewriterType: SMTEncoding =>
    // Test that a non-deterministic relation is translated to a function.
    // Importantly, consequent calls to int(2) get cached and produce the same cell in the relation.
    // A buggy implementation of DOMAIN was returning a set whose cell simultaneously belonged to the set and not.
    val set = tla.enumSet(pair(2, 3), pair(2, 10))
    val fun = tla.setAsFun(set)

    val state = new SymbState(fun, arena, Binding())
    val rewriter = create(rewriterType)
    var nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val funCell = nextState.asCell

    // probe the cells directly
    val nextArena = nextState.arena
    val relation = nextArena.getCdm(funCell)
    val relationCells = nextArena.getHas(relation)

    def isIn(no: Int): TBuilderInstruction =
      tla.selectInSet(tla.unchecked(relationCells(no).toNameEx), tla.unchecked(relation.toNameEx))

    // These checks cannot be applied to the arrays encoding because it does not have constraints for relation
    if (rewriter.solverContext.config.smtEncoding == SMTEncoding.OOPSLA19) {
      assertTlaExAndRestore(rewriter, nextState.setRex(tla.not(isIn(1))))
      assertTlaExAndRestore(rewriter, nextState.setRex(isIn(0)))
    }

    // f[2] = 3
    val app2 = tla.eql(tla.app(fun, tla.int(2)), tla.int(3))
    assertTlaExAndRestore(rewriter, nextState.setRex(app2))

    // recover the function domain
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.dom(tla.unchecked(funCell.toNameEx))))
    val funDom = nextState.asCell
    assert(solverContext.sat())

    // the domain should be equal to { 2 }
    val domEq = tla.eql(tla.unchecked(funDom.toNameEx), tla.enumSet(tla.int(2)))
    assertTlaExAndRestore(rewriter, nextState.setRex(domEq))
  }

  test("""SetAsFun({})""") { rewriterType: SMTEncoding =>
    // test that an empty set does not break things
    val set = tla.emptySet(parser("<<Int, Int>>"))
    val fun = tla.setAsFun(set)

    val state = new SymbState(fun, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val funCell = nextState.asCell

    // the domain should be equal to { }
    val domEq = tla.eql(tla.dom(tla.unchecked(funCell.toNameEx)), tla.emptySet(IntT1))
    assertTlaExAndRestore(rewriter, nextState.setRex(domEq))
  }
}
