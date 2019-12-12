package at.forsyte.apalache.tla.bmcmt.rules.deprecated

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaFunOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}


/**
  * An optimization for a record assignment: x' \in [f_1 : S_1, ..., f_n : S_n].
  * In principle, we could expand the record set first, but that is far from optimal.
  *
  * TODO: this is a case where purely symbolic constraints would help.
  *
  * Jure, 12.12.19: After changing the assignment syntax to x' <- v this rule is no longer relevant
  * TODO: Consider deleting or migrating to the new \E t \in [...] : x' = t syntax
  *
  * @author Igor Konnov
  */
@deprecated("Keramelizer and ExprOptimizer should rewrite this assignment")
class AssignRecordRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pick = new CherryPick(rewriter)

  override def isApplicable(state: SymbState): Boolean = {
    def isUnbound(name: String) =
      (!CellTheory().hasConst(name)
        && !BoolTheory().hasConst(name)
        && !IntTheory().hasConst(name)
        && !state.binding.contains(name + "'"))

    state.ex match {
      case OperEx(TlaSetOper.in,
      OperEx(TlaActionOper.prime, NameEx(name)),
      OperEx(TlaSetOper.recSet, _*)) =>
        isUnbound(name) // BUGFIX: perform an assignment if and only if name has not been assigned a value yet.

      case _ =>
        false
    }
  }

  // there is an overlap with RecordSetRule
  override def apply(state: SymbState): SymbState = {
    state.ex match {
      // x' \in [f_1 : S_1, ..., f_n : S_n]
      case OperEx(TlaSetOper.in,
      primeex @ OperEx(TlaActionOper.prime, NameEx(name)),
      ex @ OperEx(TlaSetOper.recSet, fieldsAndSets@_*)) =>
        assert(fieldsAndSets.size % 2 == 0)
        val arity = fieldsAndSets.size / 2
        assert(arity > 0)
        val fields = for ((e, i) <- fieldsAndSets.zipWithIndex; if i % 2 == 0) yield e
        val sets = for ((e, i) <- fieldsAndSets.zipWithIndex; if i % 2 == 1) yield e
        // rewrite the sets
        val (setState, setsRewritten) = rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), sets)

        // Get the types of the sets from the type finder. There are good chances that they are annotated with types.
        val recordT = findRecordType(ex, setsRewritten map setState.arena.findCellByNameEx)

        // pick a value from every set
        var nextState = setState
        def pickValue(set: TlaEx): TlaEx = {
          val cell = nextState.arena.findCellByNameEx(set)
          nextState = pick.pick(cell, nextState, nextState.arena.cellFalse().toNameEx) // TODO: no empty sets?
          nextState.ex
        }
        val pickedValues = setsRewritten map pickValue
        val fieldsAndValues: Seq[TlaEx] =
          0 until (2 * arity) map (i => if (i % 2 == 0) fields(i / 2) else pickedValues(i / 2))
        val rec = OperEx(TlaFunOper.enum, fieldsAndValues :_*)
        val assignRec = tla.in(primeex,
          tla.enumSet(tla.withType(rec, AnnotationParser.toTla(recordT))))
        rewriter.rewriteUntilDone(nextState.setRex(assignRec))

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def findRecordType(ctorEx: TlaEx, sets: Seq[ArenaCell]): CellT = {
    val fieldsAndSets: Seq[CellT] =
      0 until (2 * sets.size) map (i => if (i % 2 == 0) ConstT() else sets(i / 2).cellType)
    rewriter.typeFinder.compute(ctorEx, fieldsAndSets: _*) match {
      case FinSetT(recT@RecordT(_)) => recT
      case t@_ => throw new RewriterException("Unexpected record type: " + t)
    }
  }
}
