package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterExpand extends RewriterBase {
  test("""Expand(SUBSET {1, 2})""") { rewriterType: SMTEncoding =>
    val baseset = tla.enumSet(tla.int(1), tla.int(2))
    val expandPowset = tla.expand(tla.powSet(baseset))
    val subsets =
      tla.enumSet(tla.emptySet(IntT1), tla.enumSet(tla.int(1)), tla.enumSet(tla.int(2)),
          tla.enumSet(tla.int(1), tla.int(2)))
    val eq = tla.eql(expandPowset, subsets)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Expand([{1, 2, 3} -> {FALSE, TRUE}]) fails as unsupported""") { rewriterType: SMTEncoding =>
    val domain = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val codomain = tla.enumSet(tla.bool(false), tla.bool(true))
    val set = tla.expand(tla.funSet(domain, codomain))
    val state = new SymbState(set, arena, Binding())
    val rewriter = create(rewriterType)
    assertThrows[RewriterException](rewriter.rewriteUntilDone(state))
  }
}
