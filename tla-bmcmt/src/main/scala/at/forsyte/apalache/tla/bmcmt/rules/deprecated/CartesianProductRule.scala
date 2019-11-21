package at.forsyte.apalache.tla.bmcmt.rules.deprecated

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.MapBase
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
  * A Cartesian product S_1 × ... × S_n, which is rewritten as { &lt;&lt;x_1, ..., x_n&gt;&gt; : x_1 ∈ S_1, ..., x_n ∈ S_n}.
  * The only difference is that we do not need to add additional constraints about equality of the elements in the image,
  * as this mapping is bijective by definition.
  *
  * @author Igor Konnov
  */
@deprecated("Keramelizer takes care of that")
class CartesianProductRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val mapbase = new MapBase(rewriter, isBijective = true)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.times, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(TlaSetOper.times, sets @ _*) =>
        val arity = sets.size
        assert(arity > 0)
        val names = 0 until arity map (i => s"x_${ex.ID}_$i") // are we avoiding name collisions like that?
        val namesEs: Seq[TlaEx] = names map (s => NameEx(s))
        val namesAndSets: Seq[TlaEx] =
          0 until (2 * arity) map (i => if (i % 2 == 0) namesEs(i / 2) else sets(i / 2))
        val funEx = tla.tuple(namesEs: _*)
        val args: Seq[TlaEx] = funEx +: namesAndSets
        val map = OperEx(TlaSetOper.map, args :_*)
        val savedVarTypes = rewriter.typeFinder.getVarTypes // save the variable types, to restore them later
        rewriter.typeFinder.inferAndSave(map)
        if (rewriter.typeFinder.getTypeErrors.nonEmpty) {
          throw rewriter.typeFinder.getTypeErrors.head // throw a type inference error, if it happens
        }
        val finalState = mapbase.rewriteSetMapManyArgs(state.setRex(map), funEx, names, sets)
        rewriter.typeFinder.setVarTypes(savedVarTypes) // restore the variable types
        finalState

      case _ =>
        throw new RewriterException("%s is not applicable to %s"
          .format(getClass.getSimpleName, state.ex))
    }
  }
}
