package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.typecomp.BuilderUtil.leftTypeException
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, TBuilderTypeException, TypeComputation, TypeComputationResult}

import scala.collection.immutable.SortedMap

/**
 * Type-unsafe builder for TlaSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeSetBuilder extends ProtoBuilder {

  /** {x1, ..., xn}, must have >0 args. */
  protected def _enumSet(args: TlaEx*): TlaEx = {
    require(args.nonEmpty)
    buildBySignatureLookup(TlaSetOper.enumSet, args: _*)
  }

  /** {} : Set(elemType) */
  protected def _emptySet(elemType: TlaType1): TlaEx = OperEx(TlaSetOper.enumSet)(Typed(SetT1(elemType)))

  /** elem \in set */
  protected def _in(elem: TlaEx, set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.in, elem, set)

  /** elem \notin set */
  protected def _notin(elem: TlaEx, set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.notin, elem, set)

  /** left \cap right, left \intersect right */
  protected def _cap(left: TlaEx, right: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.cap, left, right)

  /** left \cup right, left `\`union right */
  protected def _cup(left: TlaEx, right: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.cup, left, right)

  /** UNION set */
  protected def _union(set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.union, set)

  /** { x \in set: p } */
  protected def _filter(x: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx])
    buildBySignatureLookup(TlaSetOper.filter, x, set, p)
  }

  // TODO: Consider removing, since map in the safe builder calls  mapMixed (and _mapMixed under the hood).
  /** { e: x1 \in set1 , ..., xN \in setN }, must have at least 1 var-set pair */
  protected def _map(
      e: TlaEx,
      varSetPairs: (TlaEx, TlaEx)*): TlaEx = {
    // the other _map does all the require checks
    val args = varSetPairs.flatMap { case (k, v) =>
      Seq(k, v)
    }
    _mapMixed(e, args: _*)
  }

  /**
   * Alternate call method, where pairs are passed interleaved
   *
   * @see
   *   _map[[_map(e: TlaEx, varSetPairs: (NameEx, TlaEx)*)]]
   */
  protected def _mapMixed(
      e: TlaEx,
      varSetPairs: TlaEx*): TlaEx = {
    // Even, nonzero # of args and every other argument is NameEx
    require(varSetPairs.nonEmpty)
    require(varSetPairs.size % 2 == 0)
    require(TlaOper.deinterleave(varSetPairs)._1.forall { _.isInstanceOf[NameEx] })
    buildBySignatureLookup(TlaSetOper.map, e +: varSetPairs: _*)
  }

  /** Function set constructor [fromSet -> toSet] */
  protected def _funSet(fromSet: TlaEx, toSet: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.funSet, fromSet, toSet)

  /**
   * Record set constructor [ k1: v1, ... , kN: vN ]; must have at least 1 key-value pair and all keys must be unique
   */
  protected def _recSet(kvs: (String, TlaEx)*): TlaEx = {
    // the other _recSet does all the require checks
    val args = kvs.flatMap { case (k, v) =>
      Seq(ValEx(TlaStr(k))(Typed(StrT1)), v)
    }
    _recSetMixed(args: _*)
  }

  /**
   * Alternate call method, where pairs are passed interleaved.
   *
   * @see
   *   _recSet[[_recSet(kvs: (String, TlaEx)*)]]
   */
  protected def _recSetMixed(kvs: TlaEx*): TlaEx = {
    // All keys must be ValEx(TlaStr(_))
    require(kvs.nonEmpty)
    require(kvs.size % 2 == 0)
    val recKeys = TlaOper.deinterleave(kvs)._1
    require(recKeys.forall {
      case ValEx(_: TlaStr) => true
      case _                => false
    })
    val duplicates = recKeys.filter(k => recKeys.count(_ == k) > 1)
    if (duplicates.nonEmpty)
      throw new IllegalArgumentException(s"Found repeated keys in record set constructor: ${duplicates.mkString(", ")}")

    // Record constructors don't have a signature, so we must construct a type-computation manually
    // This type computation cannot be pure, as it must read the string values of the record field names
    val typeCmp: TypeComputation = { args =>
      // read a set's element type or throw
      def getSetElemT(ex: TlaEx): TypeComputationResult =
        ex.typeTag match {
          case Typed(SetT1(t)) => t
          case other => leftTypeException(s"Expected $ex in record set constructor to have a Set(_) type, found $other")
        }

      type exOrMap = Either[TBuilderTypeException, SortedMap[String, TlaType1]]

      // Iterate over the pairs (zip), first-to-throw determines the Left value, if any.
      // If no Left appears, we get a record field-to-type map.
      // Even-indexed values should be strings, odd-indexed values should be sets
      val (keys, values) = TlaOper.deinterleave(args)
      val keyTypeMapE: exOrMap =
        keys
          .zip(values)
          .foldLeft[exOrMap](Right(SortedMap.empty)) {
            case (mapE, (ValEx(TlaStr(s)), ex)) => // key shape guaranteed by `require` check
              for {
                map <- mapE
                setElemT <- getSetElemT(ex)
              } yield map + (s -> setElemT)
            case (_, (k, _)) => // Impossible, but need to suppress warning
              Left(new TBuilderTypeException(s"Key $k is not a string literal"))
          }

      keyTypeMapE.flatMap { keyTypeMap =>
        // The result type is a set of records, the kyes of which are defined by keyTypeMap
        SetT1(RecT1(keyTypeMap))
      }
    }

    BuilderUtil.composeAndValidateTypes(TlaSetOper.recSet, typeCmp, kvs: _*)
  }

  /** Seq(set) */
  protected def _seqSet(set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.seqSet, set)

  /** left \subseteq right */
  protected def _subseteq(left: TlaEx, right: TlaEx): TlaEx =
    buildBySignatureLookup(TlaSetOper.subseteq, left, right)

  /** left \ right */
  protected def _setminus(left: TlaEx, right: TlaEx): TlaEx =
    buildBySignatureLookup(TlaSetOper.setminus, left, right)

  /** s1 \X s2 \X ... , must have >= 2 args */
  protected def _times(sets: TlaEx*): TlaEx = {
    require(sets.size >= 2)
    buildBySignatureLookup(TlaSetOper.times, sets: _*)
  }

  /** SUBSET set */
  protected def _powSet(set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.powerset, set)
}
