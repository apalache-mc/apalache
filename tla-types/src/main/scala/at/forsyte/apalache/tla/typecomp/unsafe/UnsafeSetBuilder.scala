package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.typecomp.BuilderUtil.leftTypeException
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, TBuilderTypeException, TypeComputation, TypeComputationResult}

import scala.collection.immutable.SortedMap

/**
 * Scope-unsafe builder for TlaSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeSetBuilder extends ProtoBuilder {

  /** {{{{args[0], ..., args[n]} }}} `args` must be nonempty. */
  protected def _enumSet(args: TlaEx*): TlaEx = {
    require(args.nonEmpty)
    buildBySignatureLookup(TlaSetOper.enumSet, args: _*)
  }

  /** {{{{} : Set(t)}}} */
  protected def _emptySet(t: TlaType1): TlaEx = OperEx(TlaSetOper.enumSet)(Typed(SetT1(t)))

  /** {{{elem \in set}}} */
  protected def _in(elem: TlaEx, set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.in, elem, set)

  /** {{{elem \notin set}}} */
  protected def _notin(elem: TlaEx, set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.notin, elem, set)

  /** {{{left \cap right, left \intersect right}}} */
  protected def _cap(left: TlaEx, right: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.cap, left, right)

  /** {{{left \cup right, left \union right}}} */
  protected def _cup(left: TlaEx, right: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.cup, left, right)

  /** {{{UNION set}}} */
  protected def _union(set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.union, set)

  /** {{{{ x \in set: p } }}} `x` must be a variable name */
  protected def _filter(x: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    require(x.isInstanceOf[NameEx])
    buildBySignatureLookup(TlaSetOper.filter, x, set, p)
  }

  /**
   * {{{
   * { e: pairs[0]._1 \in pairs[0]._2 , ..., pairs[n]._1 \in pairs[n]._2 } }}} `pairs` must be nonempty, and all vars
   * must be unique variable names
   */
  protected def _map(e: TlaEx, pairs: (TlaEx, TlaEx)*): TlaEx = {
    // _mapMixed does all the require checks
    val args = pairs.flatMap { case (k, v) =>
      Seq(k, v)
    }
    _mapMixed(e, args: _*)
  }

  /**
   * {{{
   * { e: pairs[0] \in pairs[1] , ..., pairs[n-1] \in pairs[n] } }}} `pairs` must have even, positive arity, and all vars
   * must be unique variable names
   */
  protected def _mapMixed(e: TlaEx, pairs: TlaEx*): TlaEx = {
    // Even, non-zero number of args and every other argument is NameEx
    require(TlaSetOper.map.arity.cond(1 + pairs.size))
    val (vars, _) = TlaOper.deinterleave(pairs)
    require(vars.forall { _.isInstanceOf[NameEx] })
    // Vars must be unique
    val duplicates = vars.filter(k => vars.count(_ == k) > 1)
    if (duplicates.nonEmpty) {
      throw new IllegalArgumentException(s"Found repeated keys in map: ${duplicates.mkString(", ")}")
    }
    buildBySignatureLookup(TlaSetOper.map, e +: pairs: _*)
  }

  /** {{{[fromSet -> toSet]}}} */
  protected def _funSet(fromSet: TlaEx, toSet: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.funSet, fromSet, toSet)

  /**
   * {{{[ kvs[0]._1: kvs[0]._2, ... , kvs[n]._1: kvs[n]._2 ]}}} `kvs` must be nonempty, and all keys must be unique
   * strings
   */
  protected def _recSet(kvs: (String, TlaEx)*): TlaEx = {
    // _recSetMixed does all the require checks
    val args = kvs.flatMap { case (k, v) =>
      Seq(ValEx(TlaStr(k))(Typed(StrT1)), v)
    }
    _recSetMixed(args: _*)
  }

  /**
   * {{{[ kvs[0]: kvs[1], ... , kvs[n-1]: kvs[n] ]}}} `kvs` must have even, positive arity, and all keys must be unique
   * strings
   */
  protected def _recSetMixed(kvs: TlaEx*): TlaEx = {
    // All keys must be ValEx(TlaStr(_))
    require(TlaSetOper.recSet.arity.cond(kvs.size))
    val (recKeys, _) = TlaOper.deinterleave(kvs)
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

  /** {{{Seq(set)}}} */
  protected def _seqSet(set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.seqSet, set)

  /** {{{left \subseteq right}}} */
  protected def _subseteq(left: TlaEx, right: TlaEx): TlaEx =
    buildBySignatureLookup(TlaSetOper.subseteq, left, right)

  /** {{{left \ right}}} */
  protected def _setminus(left: TlaEx, right: TlaEx): TlaEx =
    buildBySignatureLookup(TlaSetOper.setminus, left, right)

  /** {{{sets[0] \X sets[1] \X ... \X sets[n]}}} `sets` must have at least 2 elements */
  protected def _times(sets: TlaEx*): TlaEx = {
    require(TlaSetOper.times.arity.cond(sets.size))
    buildBySignatureLookup(TlaSetOper.times, sets: _*)
  }

  /** SUBSET set */
  protected def _powSet(set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.powerset, set)
}
