package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}

/**
 * Auxiliary methods for handling rewriting rules.
 *
 * @author
 *   Rodrigo Otoni
 */
object AuxOps {
  private lazy val simplifier = new ConstSimplifierForSmt

  /**
   * Constrains the values of a function's relation to be in line with its domain values, if the chosen SMT encoding
   * does not ensure this inherently. <p> Concretely, x \in DOMAIN \iff ((x1,y1) \in RELATION \land x = x1) \lor ...
   * \lor ((xn,yn) \in RELATION \land x = xn), with #RELATION = n.
   *
   * @param state
   *   current symbolic state
   * @param rewriter
   *   symbolic state rewriter
   * @param domain
   *   function's domain
   * @param relation
   *   function's relation
   * @return
   *   new symbolic state
   */
  def constrainRelationArgs(
      state: SymbState,
      rewriter: SymbStateRewriter,
      domain: ArenaCell,
      relation: ArenaCell): SymbState = {

    rewriter.solverContext.config.smtEncoding match {
      // If only TLA+ functions are encoded as SMT arrays, we need to propagate constraints from the set of pairs kept
      // in the arena which is used by the decoder. Without the propagation, we could have, e.g., Set1 and Set2 being
      // equal, but `5_in_Set1` not being equated to `5_in_Set2`.
      case SMTEncoding.FunArrays =>
        var nextState = state
        val domainElems = nextState.arena.getHas(domain)
        val relationElems = nextState.arena.getHas(relation)

        def eqAndInDomain(domainElem: ArenaCell, checkedElem: ArenaCell): BuilderT = {
          val eq = tla.unchecked(rewriter.lazyEq.safeEq(domainElem, checkedElem))
          val selectInSet = tla.selectInSet(domainElem.toBuilder, domain.toBuilder)
          tla.and(eq, selectInSet)
        }

        def isInDomain(elem: ArenaCell): BuilderT = {
          if (domainElems.isEmpty) {
            tla.bool(false)
          } else {
            // We check if elem is in the domain
            val elemInDomain =
              domainElems.zipAll(List.empty[ArenaCell], elem, elem).map(zip => eqAndInDomain(zip._1, zip._2))
            tla.or(elemInDomain: _*)
          }
        }

        for (tuple <- relationElems) {
          val funArg = nextState.arena.getHas(tuple).head
          val argInDomain = tla.selectInSet(funArg.toBuilder, domain.toBuilder)
          nextState = rewriter.lazyEq.cacheEqConstraints(nextState, domainElems.map((_, funArg)))
          rewriter.solverContext.declareInPredIfNeeded(domain, funArg) // inPreds might not be declared
          rewriter.solverContext.assertGroundExpr(tla.equiv(argInDomain, isInDomain(funArg)))
        }

        nextState

      case _ =>
        state
    }
  }

  /**
   * Returns the expression: checkedElem \in setCell \land checkedElem = setElem
   *
   * @param rewriter
   *   symbolic state rewriter
   * @param checkedElem
   *   element to be checked
   * @param setElem
   *   element to be compared against
   * @param setCell
   *   set to be compared against
   * @param lazyEq
   *   flag for use of lazy equality
   * @return
   *   a conjunction as described above
   */
  def inAndEq(
      rewriter: SymbStateRewriter,
      checkedElem: ArenaCell,
      setElem: ArenaCell,
      setCell: ArenaCell,
      lazyEq: Boolean): BuilderT = {

    val conjunction = if (lazyEq) {
      tla.and(
          tla.selectInSet(checkedElem.toBuilder, setCell.toBuilder),
          tla.unchecked(rewriter.lazyEq.cachedEq(checkedElem, setElem)),
      )
    } else {
      tla.and(
          tla.selectInSet(checkedElem.toBuilder, setCell.toBuilder),
          tla.eql(checkedElem.toBuilder, setElem.toBuilder),
      )
    }
    simplifier.applySimplifyShallowToBuilderEx(conjunction)
  }
}
