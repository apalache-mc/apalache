package at.forsyte.apalache.tla.typecmp.raw

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.typecmp.BuilderUtil.throwMsg
import at.forsyte.apalache.tla.typecmp.{BuilderTypeException, BuilderUtil, TypeComputation, TypeComputationReturn}

import scala.collection.immutable.SortedMap

/**
 * Raw builder for TlaSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait RawSetBuilder extends ProtoBuilder {

  /** {x1, ..., xn}, must have >0 args. */
  protected def _enumSet(arg: TlaEx, args: TlaEx*): TlaEx = simpleInstruction(TlaSetOper.enumSet, arg +: args: _*)

  /** {} : Set(elemType) */
  protected def _emptySet(elemType: TlaType1): TlaEx = OperEx(TlaSetOper.enumSet)(Typed(SetT1(elemType)))

  /** elem \in set */
  protected def _in(elem: TlaEx, set: TlaEx): TlaEx = simpleInstruction(TlaSetOper.in, elem, set)

  /** elem \notin set */
  protected def _notin(elem: TlaEx, set: TlaEx): TlaEx = simpleInstruction(TlaSetOper.notin, elem, set)

  /** left \cap right, left \intersect right */
  protected def _cap(left: TlaEx, right: TlaEx): TlaEx = simpleInstruction(TlaSetOper.cap, left, right)

  /** left \cup right, left `\`union right */
  protected def _cup(left: TlaEx, right: TlaEx): TlaEx = simpleInstruction(TlaSetOper.cup, left, right)

  /** UNION set */
  protected def _union(set: TlaEx): TlaEx = simpleInstruction(TlaSetOper.union, set)

  /** { x \in set: p } */
  protected def _filter(x: NameEx, set: TlaEx, p: TlaEx): TlaEx =
    simpleInstruction(TlaSetOper.filter, x, set, p)

  /** { e: x1 \in set1 , ..., xN \in setN }, must have at least 1 var-set pair */
  protected def _map(
      e: TlaEx,
      x1: NameEx,
      set1: TlaEx,
      pairs: TlaEx*): TlaEx = {
    // Even # of args and every other argument is NameEx
    require(pairs.size % 2 == 0)
    require(TlaOper.deinterleave(pairs)._1.forall { _.isInstanceOf[NameEx] })
    simpleInstruction(TlaSetOper.map, e +: x1 +: set1 +: pairs: _*)
  }

  /** Function set constructor [fromSet -> toSet] */
  protected def _funSet(fromSet: TlaEx, toSet: TlaEx): TlaEx = simpleInstruction(TlaSetOper.funSet, fromSet, toSet)

  /** Record set constructor [ k1: v1, ... , kN: vN ]; must have at least 1 key-value pair */
  protected def _recSet(k1: ValEx, v1: TlaEx, kvs: TlaEx*): TlaEx = {
    // All keys must be ValEx(TlaStr(_))
    require((k1 +: TlaOper.deinterleave(kvs)._1).forall {
      case ValEx(_: TlaStr) => true
      case _                => false
    })

    // Record constructors don't have a signature, so we must construct a type-computation manually
    // This type computation cannot be pure, as it must read the string values of the record field names
    val typeCmp: TypeComputation = { args =>
      // Even-indexed values should be strings, odd-indexed values should be sets
      val (keys, vals) = TlaOper.deinterleave(args)

      // read a set's element type or throw
      def getSetElemT(ex: TlaEx): TypeComputationReturn =
        ex.typeTag match {
          case Typed(SetT1(t)) => t
          case other => throwMsg(s"Expected $ex in record set constructor to have a Set(_) type, found $other")
        }

      type exOrMap = Either[BuilderTypeException, SortedMap[String, TlaType1]]

      // Iterate over the pairs (zip), first-to-throw determines the Left value, if any.
      // If no Left appears, we get a record field-to-type map.
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
        // We already know all odd-index values are sets and all even-indexed are strings by
        // require (or construction, in the string-argument method variant)
        // so we can just map fromTypeTag over the args
        OperT1(args.map { ex => TlaType1.fromTypeTag(ex.typeTag) }, SetT1(RecT1(keyTypeMap)))
      }
    }

    BuilderUtil.buildInstruction(TlaSetOper.recSet, typeCmp, k1 +: v1 +: kvs: _*)
  }

  /**
   * Alternate call method, where Scala strings are passed in place of ValEx(TlaStr(_))
   * @see
   *   _recSet[[_recSet(k1: ValEx, v1: TlaEx, kvs: TlaEx*)]]
   */
  protected def _recSet(kv1: (String, TlaEx), kvs: (String, TlaEx)*): TlaEx = {
    val (k1, v1) = kv1
    def toStrEx(s: String): ValEx = ValEx(TlaStr(s))(Typed(StrT1()))
    val args = kvs.flatMap { case (k, v) =>
      Seq(toStrEx(k), v)
    }
    _recSet(toStrEx(k1), v1, args: _*)
  }

  /** Seq(set) */
  protected def _seqSet(set: TlaEx): TlaEx = simpleInstruction(TlaSetOper.seqSet, set)

  /** left \subseteq right */
  protected def _subseteq(left: TlaEx, right: TlaEx): TlaEx =
    simpleInstruction(TlaSetOper.subseteq, left, right)

  /** left \ right */
  protected def _setminus(left: TlaEx, right: TlaEx): TlaEx =
    simpleInstruction(TlaSetOper.setminus, left, right)

  /** s1 \X s2 \X ... */
  protected def _times(s1: TlaEx, s2: TlaEx, sets: TlaEx*): TlaEx =
    simpleInstruction(TlaSetOper.times, s1 +: s2 +: sets: _*)

  /** SUBSET set */
  protected def _powSet(set: TlaEx): TlaEx = simpleInstruction(TlaSetOper.powerset, set)
}
