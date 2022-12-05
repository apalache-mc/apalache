package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.rules.aux.{ProtoSeqOps, RecordAndVariantOps}
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.{tla, ModelValueHandler}
import com.typesafe.scalalogging.LazyLogging

import scala.collection.immutable.SortedMap

/**
 * This class dumps relevant values from an SMT model using an arena.
 *
 * @author
 *   Igor Konnov
 */
class SymbStateDecoder(solverContext: SolverContext, rewriter: SymbStateRewriter) extends LazyLogging {
  private val protoSeqOps = new ProtoSeqOps(rewriter)
  private val recordOps = new RecordAndVariantOps(rewriter)

  def decodeStateVariables(state: SymbState): Map[String, TlaEx] = {
    state.binding.toMap.map(p => (p._1, reverseMapVar(decodeCellToTlaEx(state.arena, p._2), p._1, p._2)))
  }

  def decodeCellToTlaEx(arena: PureArenaAdapter, cell: ArenaCell): TBuilderInstruction = cell.cellType match {
    case CellTFrom(BoolT1) =>
      cell.toBuilder.map(solverContext.evalGroundExpr)

    case CellTFrom(IntT1) =>
      cell.toBuilder.map(solverContext.evalGroundExpr)

    case tt @ (CellTFrom(ConstT1(_)) | CellTFrom(StrT1)) =>
      // First, attempt to check the cache
      val found = rewriter.modelValueCache.findKey(cell)
      if (found.isDefined) {
        val pa @ (_, index) = found.get
        if (tt == CellTFrom(StrT1)) tla.str(index)
        else tla.constParsed(ModelValueHandler.construct(pa))
      } else {
        // if not in the cache, it might be the case that another cell, which has asserted equivalence
        // with the original cell can be found
        val values = rewriter.modelValueCache.values().filter(_.cellType == tt).toSeq
        findCellInSet(values, cell.toBuilder) match {
          // found among the cached keys
          case Some(c) =>
            decodeCellToTlaEx(arena, c)

          case None =>
            // not found, just use the name
            // a value that was assigned by the solver, and not created by us
            tla.str(cell.toString)
        }
      }

    case UnknownT() =>
      throw new IllegalStateException(s"Found cell $cell of cell type Unknown")

    case CellTFrom(SetT1(_)) =>
      def inSet(e: ArenaCell) = {
        val mem = tla.selectInSet(e.toBuilder, cell.toBuilder)
        solverContext.evalGroundExpr(mem) == tla.bool(true).build
      }

      val elems = arena.getHas(cell).filter(inSet)
      val decodedElems = elems.map(decodeCellToTlaEx(arena, _).build)
      // try to normalize the set for better user experience
      val niceElems = decodedElems.distinct.sortWith(SymbStateDecoder.compareTlaExByStr).map(tla.unchecked)
      tla.enumSet(niceElems: _*)

    case FinFunSetT(_, _) =>
      val fromSet = decodeCellToTlaEx(arena, arena.getDom(cell))
      val toSet = decodeCellToTlaEx(arena, arena.getCdm(cell))
      tla.funSet(fromSet, toSet)

    case CellTFrom(FunT1(_, _)) =>
      decodeFunToTlaEx(arena, cell)

    case CellTFrom(SeqT1(elemT1)) =>
      val (protoSeq, lenCell, capacity) = protoSeqOps.unpackSeq(arena, cell)
      val len = decodeCellToTlaEx(arena, lenCell).build match {
        case ValEx(TlaInt(n)) =>
          // if the length value is corrupt, adjust it
          if (n < 0 || n > capacity) {
            logger.warn(s"Sequence length should belong to 0..$capacity, found: $n")
            Math.min(Math.max(0, n.toInt), capacity)
          } else {
            n.toInt
          }
        case ex => throw new RewriterException("Expected an int, found " + ex, ex)
      }
      val decodedElems = protoSeqOps.elems(arena, protoSeq).map(decodeCellToTlaEx(arena, _)).toList.slice(0, len)
      if (decodedElems.isEmpty) tla.emptySeq(elemT1)
      else tla.seq(decodedElems: _*)

    case CellTFrom(recT @ RecT1(_)) =>
      decodeOldRecordToTlaEx(arena, cell, recT)

    case CellTFrom(RecRowT1(RowT1(fieldTypes, None))) =>
      decodeRecordToTlaEx(arena, cell, fieldTypes)

    case CellTFrom(VariantT1(RowT1(options, None))) =>
      decodeVariantToTlaEx(arena, cell, options)

    case CellTFrom(_: TupT1) =>
      val tupleElems = arena.getHas(cell)
      val elemAsExprs = tupleElems.map(c => decodeCellToTlaEx(arena, c))
      tla.tuple(elemAsExprs: _*)

    case PowSetT(SetT1(_)) =>
      val baseset = decodeCellToTlaEx(arena, arena.getDom(cell))
      tla.powSet(baseset)

    case InfSetT(_) if cell == arena.cellIntSet() =>
      tla.intSet()

    case InfSetT(_) if cell == arena.cellNatSet() =>
      tla.natSet()

    case _ =>
      throw new RewriterException("Don't know how to decode the cell %s of type %s".format(cell, cell.cellType), NullEx)
  }

  private def decodeOldRecordToTlaEx(arena: PureArenaAdapter, cell: ArenaCell, recordT: RecT1): TBuilderInstruction = {
    def exToStr(ex: TlaEx): TlaStr = ex match {
      case ValEx(s @ TlaStr(_)) => s
      case _                    => throw new RewriterException("Expected a string, found: " + ex, ex)
    }

    // Note that the domain may have fewer fields than the record type is saying.
    // This comes from the fact that we can extend a record with a richer type.
    val domCell = arena.getDom(cell)
    val dom = decodeSet(arena, domCell).map(exToStr)
    val fieldValues = arena.getHas(cell)
    val keyList = recordT.fieldTypes.keySet.toList

    def eachField(es: List[TBuilderInstruction], key: String): List[TBuilderInstruction] = {
      if (!dom.contains(TlaStr(key))) {
        es // skip
      } else {
        val index = keyList.indexOf(key)
        val valueCell = fieldValues(index)
        tla.str(key) +: decodeCellToTlaEx(arena, valueCell) +: es
      }
    }

    val keysAndValues = keyList.reverse.foldLeft(List.empty[TBuilderInstruction])(eachField)
    if (keysAndValues.nonEmpty) {
      tla.recMixed(keysAndValues: _*)
    } else {
      logger.error(
          s"Decoder: Found an empty record $cell when decoding a counterexample, domain = $domCell. This is a bug.")
      // for debugging purposes, just return a string
      tla.str(s"Empty record domain $domCell")
    }
  }

  private def decodeRecordToTlaEx(
      arena: PureArenaAdapter,
      cell: ArenaCell,
      fieldTypes: SortedMap[String, TlaType1]): TBuilderInstruction =
    tla.rec(fieldTypes.keySet.toList.map { k =>
      k -> decodeCellToTlaEx(arena, recordOps.getField(arena, cell, k))
    }: _*)

  private def decodeVariantToTlaEx(
      arena: PureArenaAdapter,
      cell: ArenaCell,
      options: SortedMap[String, TlaType1]): TBuilderInstruction = {
    val tagName = decodeCellToTlaEx(arena, recordOps.getVariantTag(arena, cell)).build match {
      case ValEx(TlaStr(name)) => name

      case e => throw new RewriterException(s"Expected a tag name in a variant $cell, found: $e", NullEx)
    }
    val value = decodeCellToTlaEx(arena, recordOps.getUnsafeVariantValue(arena, cell, tagName))
    tla.variant(tagName, value, VariantT1(RowT1(options, None)))
  }

  private def decodeFunToTlaEx(arena: PureArenaAdapter, cell: ArenaCell): TBuilderInstruction = {
    // a function is represented with the relation {(x, f[x]) : x \in S}
    val relation = arena.getCdm(cell)

    def isInRelation(pair: ArenaCell): Boolean = {
      solverContext.config.smtEncoding match {
        case SMTEncoding.Arrays | SMTEncoding.FunArrays =>
          // in the arrays encoding the relation is only represented in the arena
          // given this, we query the solver about the function's domain instead
          val domain = arena.getDom(cell)

          def inDom(elem: ArenaCell): TBuilderInstruction = {
            val elemEx = elem.toBuilder
            val domEx = domain.toBuilder
            tla.selectInSet(elemEx, domEx)
          }

          // check if the pair's head is in the domain
          val funArg = arena.getHas(pair).head
          val argsInDom = inDom(funArg)
          solverContext.evalGroundExpr(argsInDom) == tla.bool(true).build

        case SMTEncoding.OOPSLA19 =>
          val mem = tla.selectInSet(pair.toBuilder, relation.toBuilder)
          solverContext.evalGroundExpr(mem) == tla.bool(true).build

        case oddEncodingType =>
          throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
      }
    }

    def decodePair(seen: Map[TlaEx, TlaEx], pair: ArenaCell): Map[TlaEx, TlaEx] = {
      val keyCell :: valueCell :: _ = arena.getHas(pair)
      val keyEx = decodeCellToTlaEx(arena, keyCell)
      if (seen.contains(keyEx)) {
        seen
      } else {
        val valueEx = decodeCellToTlaEx(arena, valueCell)
        seen + (keyEx.build -> valueEx.build)
      }
    }

    val pairs = arena
      .getHas(relation)
      .filter(isInRelation)
      .foldLeft(Map.empty[TlaEx, TlaEx])(decodePair)
      .toSeq
      .map { case (k, v) => tla.tuple(tla.unchecked(k), tla.unchecked(v)) }

    tla.setAsFun(tla.enumSet(pairs: _*))
  }

  private def decodeSet(arena: PureArenaAdapter, set: ArenaCell): Seq[TlaEx] = {
    decodeCellToTlaEx(arena, set).build match {
      case OperEx(TlaSetOper.enumSet, elems @ _*) =>
        elems

      case _ =>
        throw new RewriterException("Unexpected domain structure: " + set, NullEx)
    }
  }

  private def findCellInSet(cells: Seq[ArenaCell], ex: TBuilderInstruction): Option[ArenaCell] = {
    def isEq(c: ArenaCell): Boolean = {
      val query = tla.and(tla.eql(c.toBuilder, ex))
      tla.bool(true).build == solverContext.evalGroundExpr(query)
    }

    cells.find(isEq)
  }

  def reverseMapVar(expr: TlaEx, varName: String, cell: ArenaCell): TlaEx = {
    def rec(ex: TlaEx): TlaEx = ex match {
      case NameEx(name) =>
        if (name != cell.toNameEx.name) {
          ex
        } else {
          NameEx(varName)(ex.typeTag)
        }

      case OperEx(oper, args @ _*) =>
        OperEx(oper, args.map(rec): _*)(ex.typeTag)

      case _ =>
        ex
    }

    rec(expr)
  }
}

object SymbStateDecoder {
  private def compareTlaExByStr(lhs: TlaEx, rhs: TlaEx): Boolean =
    lhs.toString.compareTo(rhs.toString) <= 0
}
