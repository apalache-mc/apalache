package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.RecordT
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, ValEx}

import scala.collection.immutable.SortedMap

/**
  * Implements the rules: SE-REC-CTOR[1-2].
  *
  * Internally, a record is stored as a tuple,
  * where an index i corresponds to the ith key in the sorted set of record keys.
  *
  * @author Igor Konnov
  */
class RecCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.enum, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.enum, elems @ _*) =>
        val keyEs = elems.zipWithIndex.filter(_._2 % 2 == 0).map(_._1) // pick the even indices (starting with 0)
        val keys = keysToStr(keyEs.toList)
        val valueEs = elems.zipWithIndex.filter(_._2 % 2 == 1).map(_._1) // pick the odd indices (starting with 0)
        assert(keyEs.lengthCompare(valueEs.length) == 0)

        // create a tuple that stores the values
        val tupleState =
          rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(tla.tuple(valueEs :_*)))

        val tupleCell = tupleState.arena.findCellByNameEx(tupleState.ex)
        val elemTypes = tupleState.arena.getHas(tupleCell).map(_.cellType)

        // create the record cell and connect it to the fresh tuple
        val recordType = RecordT(SortedMap(keys.zip(elemTypes) :_*))
        var arena = tupleState.arena.appendCell(recordType)
        val record = arena.topCell
        arena = arena.appendHas(record, tupleCell)

        val finalState = tupleState.setArena(arena).setRex(record.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def keysToStr(keys: List[TlaEx]): List[String] = {
    def eachKey(k: TlaEx) = k match {
      case ValEx(TlaStr(str)) =>
        str

      case _ =>
        throw new RewriterException("Expected a string as a record key, found: " + k)
    }

    keys map eachKey
  }
}
