package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.arena.{PureArenaAdapter, SmtConstElemPtr}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, SymbStateRewriter}
import at.forsyte.apalache.tla.lir._

import scala.collection.immutable.SortedSet

/**
 * Given a type, this class produces a default value for that type. This is needed by ChooseRule and FunAppRule.
 *
 * @author
 *   Igor Konnov
 */
class DefaultValueFactory(rewriter: SymbStateRewriter) {
  private val protoSeqOps = new ProtoSeqOps(rewriter)

  /**
   * Produce a default value that, for instance, can be used as a value when picking from an empty set.
   *
   * @param arena
   *   an arena to start with
   * @param valueType
   *   the type of the value to be created
   * @return
   *   a new symbolic state that contains the new value as the expression
   */
  def makeUpValue(arena: PureArenaAdapter, valueType: TlaType1): (PureArenaAdapter, ArenaCell) = {
    valueType match {
      case IntT1 =>
        rewriter.intValueCache.getOrCreate(arena, 0)

      case BoolT1 =>
        (arena, arena.cellFalse())

      case StrT1 =>
        rewriter.modelValueCache.getOrCreate(arena, (StrT1.toString(), "None"))

      case ConstT1(utype) =>
        rewriter.modelValueCache.getOrCreate(arena, (utype, "None"))

      case tupT @ TupT1(argTypes @ _*) =>
        var newArena = arena.appendCell(tupT)
        val tuple = newArena.topCell
        newArena = argTypes.foldLeft(newArena) { (arena, argT) =>
          val (nextArena, valueCell) = makeUpValue(arena, argT)
          nextArena.appendHasNoSmt(tuple, SmtConstElemPtr(valueCell)) // made-up cell = ConstElemPtr
        }
        (newArena, tuple)

      case recT @ RecT1(_) =>
        var newArena = arena.appendCell(recT)
        val recCell = newArena.topCell
        newArena = recT.fieldTypes.values.foldLeft(newArena) { (arena, v) =>
          val (nextArena, valueCell) = makeUpValue(arena, v)
          nextArena.appendHasNoSmt(recCell, SmtConstElemPtr(valueCell)) // made-up cell = ConstElemPtr
        }
        // create the domain and attach it to the record
        val pairOfSets = (recT.fieldTypes.keySet, SortedSet[String]())
        val (nextArena, domain) =
          rewriter.recordDomainCache.getOrCreate(newArena, pairOfSets)
        newArena = nextArena.setDom(recCell, domain)
        (newArena, recCell)

      case recordT @ RecRowT1(RowT1(fieldTypes, _)) =>
        var newArena = arena.appendCell(recordT)
        val recCell = newArena.topCell
        newArena = fieldTypes.values.foldLeft(newArena) { (arena, v) =>
          val (nextArena, valueCell) = makeUpValue(arena, v)
          nextArena.appendHasNoSmt(recCell, SmtConstElemPtr(valueCell)) // made-up cell = ConstElemPtr
        }
        (newArena, recCell)

      case tp @ SetT1(_) => // {}
        val newArena = arena.appendCell(tp)
        (newArena, newArena.topCell)

      case tp @ FunT1(argT, resT) => // [x \in {} |-> {}]
        val (arena1, domCell) = makeUpValue(arena, SetT1(argT))
        val (arena2, relCell) = makeUpValue(arena1, SetT1(TupT1(argT, resT)))
        val arena3 = arena2.appendCell(tp)
        val funCell = arena3.topCell
        val arena4 = arena3.setDom(funCell, domCell).setCdm(funCell, relCell)
        (arena4, funCell)

      case tp @ SeqT1(_) => // << >>
        // make an empty proto sequence
        val (arena2, protoSeq) = protoSeqOps.makeEmptyProtoSeq(arena)
        val (arena3, zero) = rewriter.intValueCache.create(arena2, 0)
        protoSeqOps.mkSeqCell(arena3, tp, protoSeq, zero)

      case variantT @ VariantT1(RowT1(options, None)) if options.nonEmpty =>
        // it would be better to call RecordAndVariantOps.makeVariant, but that would produce a circular dependency
        val tagName = options.head._1
        val (arena2, tagAsCell) = rewriter.modelValueCache.getOrCreate(arena, (StrT1.toString, tagName))
        var nextArena = arena2
        // introduce default values for all variant options
        val variantValues = options.map { case (t, tp) =>
          val (newArena, defaultValue) = makeUpValue(nextArena, tp)
          nextArena = newArena
          (t, defaultValue)
        }
        // introduce a cell for the variant and wire the values to it
        nextArena = nextArena.appendCell(variantT)
        val variantCell = nextArena.topCell
        for (fieldCell <- (variantValues + (RecordAndVariantOps.variantTagField -> tagAsCell)).valuesIterator) {
          nextArena = nextArena.appendHasNoSmt(variantCell, SmtConstElemPtr(fieldCell)) // made-up cell = ConstElemPtr
        }

        (nextArena, variantCell)

      case tp @ _ =>
        throw new RewriterException(s"Unexpected type $tp when generating a default value", NullEx)
    }
  }
}
