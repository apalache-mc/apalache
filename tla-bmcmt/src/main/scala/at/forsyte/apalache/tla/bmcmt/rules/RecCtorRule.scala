package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.DefaultValueFactory
import at.forsyte.apalache.tla.bmcmt.types.{CellT, ConstT, RecordT}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, ValEx}

import scala.collection.immutable.SortedSet

/**
  * Rewrites a record constructor [f_1 |-> e_1, ..., f_k |-> e_k].
  *
  * Internally, a record is stored as a tuple,
  * where an index i corresponds to the ith key in the sorted set of record keys.
  *
  * Note that one can extend a record with a type annotation, e.g.,
  * the expression [a |-> 1] <: [a |-> Int, b |-> BOOLEAN] introduces a record r of two fields (a: Int and b: BOOLEAN).
  * The value r.a is defined as 1, whereas r.b is arbitrary.
  *
  * @author Igor Konnov
  */
class RecCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val defaultValueFactory = new DefaultValueFactory(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.enum, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.enum, elems@_*) =>
        val keyEs = elems.zipWithIndex.filter(_._2 % 2 == 0).map(_._1) // pick the even indices (starting with 0)
        val ctorKeys = keysToStr(state.ex, keyEs.toList)
        val valueEs = elems.zipWithIndex.filter(_._2 % 2 == 1).map(_._1) // pick the odd indices (starting with 0)
        assert(keyEs.lengthCompare(valueEs.length) == 0)
        // rewrite the values, we need it to compute the record type with typeFinder
        val (newState: SymbState, newValues: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), valueEs)
        // compute the types of the field values and then use the type finder
        val valueCells = newValues.map(newState.arena.findCellByNameEx)
        val typeArgs = elems.zipWithIndex.map(p => if (p._2 % 2 == 0) ConstT() else valueCells(p._2 / 2).cellType)
        val recordT = rewriter.typeFinder.compute(state.ex, typeArgs: _*).asInstanceOf[RecordT]
        // the computed record type may contain additional keys, due to a type annotation
        var arena = newState.arena.appendCell(recordT)
        val recordCell = arena.topCell
        // importantly, the record keys that are outside of ctorKeys should not belong to the domain!
        val extraKeys = recordT.fields.keySet.filter(k => !ctorKeys.contains(k))
        def addExtra(map: Map[String, ArenaCell], key: String) = {
          // make sure that the key is cached, as it does not appear in the actual expression
          val (newArena, keyCell) = rewriter.strValueCache.getOrCreate(arena, key)
          arena = newArena
          map + (key -> keyCell)
        }
        // map these extra keys to the respective cells
        val extraKeyMap = extraKeys.foldLeft(Map.empty[String, ArenaCell])(addExtra)

        var nextState = newState.setArena(arena)
        // Connect the value cells to the record. The edges come in the order of allKeys. If the actual record passed
        // in the constructor does not contain a key, we add a default value of the required type.
        // It is important to add default values to preserve the structure of the cells, e.g.,
        // empty sequences require two cells: start and end.
        def addField(key: String, tp: CellT): Unit = {
          val valueCell =
            if (ctorKeys.contains(key)) {
              valueCells(ctorKeys.indexOf(key)) // get the cell associated with the value
            } else {
              // produce a default value
              nextState = defaultValueFactory.makeUpValue(nextState, tp)
              nextState.asCell
            }
          // link this cell to the record
          nextState = nextState.updateArena(_.appendHasNoSmt(recordCell, valueCell))
        }

        recordT.fields foreach Function.tupled(addField)

        // Create the domain cell. Note that the actual domain may have fewer keys than recordT.fields.keys
        val (newArena, domain) =
          rewriter.recordDomainCache.getOrCreate(nextState.arena, (SortedSet(ctorKeys :_*), extraKeys))
        nextState = nextState.setArena(newArena.setDom(recordCell, domain))
        // importantly, the record keys that are outside of ctorKeys should not belong to the domain!
        if (extraKeyMap.nonEmpty) {
          val extraOutsideOfDomain = extraKeyMap.values.map(f => tla.notin(f.toNameEx, domain.toNameEx))
          rewriter.solverContext.assertGroundExpr(tla.and(extraOutsideOfDomain.toSeq :_*))
        }

        val finalState = nextState.setRex(recordCell.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def keysToStr(ex: TlaEx, keys: List[TlaEx]): List[String] = {
    def eachKey(k: TlaEx) = k match {
      case ValEx(TlaStr(str)) =>
        str

      case _ =>
        throw new RewriterException("Expected a string as a record key, found: " + k, ex)
    }

    keys map eachKey
  }
}
