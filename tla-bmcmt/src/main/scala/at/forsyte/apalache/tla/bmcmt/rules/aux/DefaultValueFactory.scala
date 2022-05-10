package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell, RewriterException, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, FunT1, IntT1, NullEx, RecT1, SeqT1, SetT1, StrT1, TlaType1, TupT1}

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
  def makeUpValue(arena: Arena, valueType: TlaType1): (Arena, ArenaCell) = {
    valueType match {
      case IntT1() =>
        rewriter.intValueCache.getOrCreate(arena, 0)

      case BoolT1() =>
        (arena, arena.cellFalse())

      case StrT1() =>
        rewriter.modelValueCache.getOrCreate(arena, (StrT1().toString(), "None"))

      case ConstT1(utype) =>
        rewriter.modelValueCache.getOrCreate(arena, (utype, "None"))

      case tupT @ TupT1(argTypes @ _*) =>
        var newArena = arena.appendCell(tupT)
        val tuple = newArena.topCell
        newArena = argTypes.foldLeft(newArena) { (arena, argT) =>
          val (nextArena, valueCell) = makeUpValue(arena, argT)
          nextArena.appendHasNoSmt(tuple, valueCell)
        }
        (newArena, tuple)

      case recT @ RecT1(_) =>
        var newArena = arena.appendCell(recT)
        val recCell = newArena.topCell
        newArena = recT.fieldTypes.values.foldLeft(newArena) { (arena, v) =>
          val (nextArena, valueCell) = makeUpValue(arena, v)
          nextArena.appendHasNoSmt(recCell, valueCell)
        }
        // create the domain and attach it to the record
        val pairOfSets = (recT.fieldTypes.keySet, SortedSet[String]())
        val (nextArena, domain) =
          rewriter.recordDomainCache.getOrCreate(newArena, pairOfSets)
        newArena = nextArena.setDom(recCell, domain)
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

      case tp @ _ =>
        throw new RewriterException(s"Unexpected type $tp when generating a default value", NullEx)
    }
  }
}
