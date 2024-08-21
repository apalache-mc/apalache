package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.RecordAndVariantOps
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.types.{tlaU => tla}

import scala.collection.immutable.{SortedMap, SortedSet}

/**
 * Rewrites a record constructor [f_1 |-> e_1, ..., f_k |-> e_k].
 *
 * Internally, a record is stored as a tuple, where an index i corresponds to the ith key in the sorted set of record
 * keys.
 *
 * @author
 *   Igor Konnov
 */
class RecCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val recordOps = new RecordAndVariantOps(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.rec, _*) => true
      case _                          => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(TlaFunOper.rec, elems @ _*) =>
        val keyEs = elems.zipWithIndex.filter(_._2 % 2 == 0).map(_._1) // pick the even indices (starting with 0)
        val ctorKeys = keysToStr(state.ex, keyEs.toList)
        val valueEs = elems.zipWithIndex.filter(_._2 % 2 == 1).map(_._1) // pick the odd indices (starting with 0)
        assert(keyEs.lengthCompare(valueEs.length) == 0)
        // rewrite the values, we need it to compute the record type with typeFinder
        val (newState: SymbState, newValues: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state, valueEs)
        // compute the types of the field values and then use the type finder
        val valueCells = newValues.map(newState.arena.findCellByNameEx)

        // the record type may contain more fields than passed in the arguments
        TlaType1.fromTypeTag(ex.typeTag) match {
          case recordT @ RecT1(_) =>
            makeOldRecord(newState, recordT, ctorKeys, valueCells)

          case RecRowT1(RowT1(_, _)) =>
            recordOps.makeRecord(newState, SortedMap(ctorKeys.zip(valueCells): _*))

          case tt =>
            throw new IllegalStateException("Unexpected type of a constructed record: " + tt)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def makeOldRecord(
      state: SymbState,
      recordT: RecT1,
      fieldNames: List[String],
      valueCells: Seq[ArenaCell]): SymbState = {
    var arena = state.arena.appendCell(recordT)
    val recordCell = arena.topCell
    // importantly, the record keys that are outside of ctorKeys should not belong to the domain!
    val extraKeys = recordT.fieldTypes.keySet.filter(k => !fieldNames.contains(k))

    def addExtra(map: Map[String, ArenaCell], key: String) = {
      // make sure that the key is cached, as it does not appear in the actual expression
      val (newArena, keyCell) = rewriter.modelValueCache.getOrCreate(arena, (StrT1.toString, key))
      arena = newArena
      map + (key -> keyCell)
    }

    // map these extra keys to the respective cells
    val extraKeyMap = extraKeys.foldLeft(Map.empty[String, ArenaCell])(addExtra)

    var nextState = state.setArena(arena)

    // Connect the value cells to the record. The edges come in the order of allKeys. If the actual record passed
    // in the constructor does not contain a key, we add a default value of the required type.
    // It is important to add default values to preserve the structure of the cells, e.g.,
    // empty sequences require two cells: start and end.
    def addField(key: String, tp: TlaType1): Unit = {
      val valueCell =
        if (fieldNames.contains(key)) {
          valueCells(fieldNames.indexOf(key)) // get the cell associated with the value
        } else {
          // produce a default value
          val (newArena, defaultValue) = rewriter.defaultValueCache.getOrCreate(nextState.arena, tp)
          nextState = nextState.setArena(newArena)
          defaultValue
        }
      // link this cell to the record
      nextState = nextState.updateArena(_.appendHasNoSmt(recordCell, FixedElemPtr(valueCell)))
    }

    for ((key, tp) <- recordT.fieldTypes) {
      addField(key, tp)
    }

    // Create the domain cell. Note that the actual domain may have fewer keys than recordT.fields.keys
    val (newArena, domain) =
      rewriter.recordDomainCache.getOrCreate(nextState.arena, (SortedSet(fieldNames: _*), extraKeys))
    nextState = nextState.setArena(newArena.setDom(recordCell, domain))
    // importantly, the record keys that are outside of ctorKeys should not belong to the domain!
    if (extraKeyMap.nonEmpty) {
      val extraOutsideOfDomain =
        extraKeyMap.values.map(f => tla.not(tla.selectInSet(f.toBuilder, domain.toBuilder)))
      rewriter.solverContext.assertGroundExpr(tla.and(extraOutsideOfDomain.toSeq: _*))
    }

    nextState.setRex(recordCell.toBuilder)
  }

  private def keysToStr(ex: TlaEx, keys: List[TlaEx]): List[String] = {
    def eachKey(k: TlaEx) = k match {
      case ValEx(TlaStr(str)) =>
        str

      case _ =>
        throw new RewriterException("Expected a string as a record key, found: " + k, ex)
    }

    keys.map(eachKey)
  }
}
