package at.forsyte.apalache.tla.typecmp.raw

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.typecmp.BuilderUtil.throwMsg
import at.forsyte.apalache.tla.typecmp.{typeComputation, typeComputationReturn, BuildInstruction, BuilderTypeException}

import scala.collection.immutable.SortedMap

/**
 * @author
 *   Jure Kukovec
 */
trait RawSetBuilder extends ProtoBuilder {

  // Must have 1+ args
  protected def _enumSet(arg: TlaEx, args: TlaEx*): TlaEx =
    simpleInstruction(TlaSetOper.enumSet, 1 + args.size).build(arg +: args: _*)

  protected def _emptySet(elemType: TlaType1): TlaEx = OperEx(TlaSetOper.enumSet)(Typed(SetT1(elemType)))

  protected def _in(elem: TlaEx, set: TlaEx): TlaEx = simpleInstruction(TlaSetOper.in, 2).build(elem, set)

  protected def _notin(elem: TlaEx, set: TlaEx): TlaEx = simpleInstruction(TlaSetOper.notin, 2).build(elem, set)

  protected def _cap(left: TlaEx, right: TlaEx): TlaEx = simpleInstruction(TlaSetOper.cap, 2).build(left, right)

  protected def _cup(left: TlaEx, right: TlaEx): TlaEx = simpleInstruction(TlaSetOper.cup, 2).build(left, right)

  protected def _union(set: TlaEx): TlaEx = simpleInstruction(TlaSetOper.union, 1).build(set)

  protected def _filter(x: NameEx, set: TlaEx, p: TlaEx): TlaEx =
    simpleInstruction(TlaSetOper.filter, 3).build(x, set, p)

  protected def _map(
      mapExpr: TlaEx,
      var1: NameEx,
      set1: TlaEx,
      varsAndSetsInterleaved: TlaEx*): TlaEx = {
    // Every other argument is NameEx
    require(TlaOper.deinterleave(varsAndSetsInterleaved)._1.forall { _.isInstanceOf[NameEx] })
    simpleInstruction(TlaSetOper.map, 3 + varsAndSetsInterleaved.size).build(
        mapExpr +: var1 +: set1 +: varsAndSetsInterleaved: _*
    )
  }

  protected def _funSet(fromSet: TlaEx, toSet: TlaEx): TlaEx =
    simpleInstruction(TlaSetOper.funSet, 2).build(fromSet, toSet)

  protected def _recSet(kv1: (String, TlaEx), kvs: (String, TlaEx)*): TlaEx = {
    val typeCmp: typeComputation = { args =>
      // Even-indexed values should be strings, odd-indexed values should be sets
      val (keys, vals) = TlaOper.deinterleave(args)

      // read a set's element type or throw
      def getSetElemT(ex: TlaEx): typeComputationReturn =
        ex.typeTag match {
          case Typed(SetT1(t)) => t
          case other           => throwMsg(s"Expected $ex to have a Set(_) type, found $other")
        }

      type exOrMap = Either[BuilderTypeException, SortedMap[String, TlaType1]]

      // Iterate over the pairs (zip), first-to-throw determines the Left value, if any
      // If no Left appears, we get a record field-to-type map
      val keyTypeMapE: exOrMap =
        keys
          .zip(vals)
          .foldLeft[exOrMap](Right(SortedMap.empty)) {
            case (mapE, (ValEx(TlaStr(s)), ex)) => // key shape guaranteed by construction
              for {
                map <- mapE
                setElemT <- getSetElemT(ex)
              } yield map + (s -> setElemT)
            case (_, (k, _)) => // Impossible, but need to suppress warning
              Left(new BuilderTypeException(s"Key $k is not a string"))
          }

      keyTypeMapE.flatMap { keyTypeMap =>
        // We already know all odd-index values are sets and all even-indexed are strings by construction,
        // so we can just map fromTypeTag over the args
        OperT1(args.map { ex => TlaType1.fromTypeTag(ex.typeTag) }, RecT1(keyTypeMap))
      }
    }

    val args = (kv1 +: kvs).flatMap { case (k, v) =>
      Seq(ValEx(TlaStr(k))(Typed(StrT1())), v)
    }

    BuildInstruction(TlaSetOper.recSet, typeCmp).build(args: _*)
  }

  protected def _seqSet(set: TlaEx): TlaEx = simpleInstruction(TlaSetOper.seqSet, 1).build(set)

  protected def _subseteq(left: TlaEx, right: TlaEx): TlaEx =
    simpleInstruction(TlaSetOper.subseteq, 2).build(left, right)

  protected def _setminus(left: TlaEx, right: TlaEx): TlaEx =
    simpleInstruction(TlaSetOper.setminus, 2).build(left, right)

  protected def _times(s1: TlaEx, s2: TlaEx, sets: TlaEx*): TlaEx =
    simpleInstruction(TlaSetOper.times, 2 + sets.size).build(s1 +: s2 +: sets: _*)

  protected def _powSet(set: TlaEx): TlaEx = simpleInstruction(TlaSetOper.powerset, 1).build(set)

}
