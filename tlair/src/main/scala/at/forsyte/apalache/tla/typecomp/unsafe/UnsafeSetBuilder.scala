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
trait UnsafeSetBuilder extends ProtoBuilder with UnsafeLiteralAndNameBuilder {
  // We extend the LiteralBuilder to make TLA strings from Scala strings

  /**
   * {{{
   * {args[0], ..., args[n]} }}} To construct empty sets, use [[emptySet]] instead.
   * @param args
   *   must be nonempty.
   */
  def enumSet(args: TlaEx*): TlaEx = {
    require(args.nonEmpty, s"args must be nonempty.")
    buildBySignatureLookup(TlaSetOper.enumSet, args: _*)
  }

  /** {{{{} : Set(t)}}} */
  def emptySet(t: TlaType1): TlaEx = OperEx(TlaSetOper.enumSet)(Typed(SetT1(t)))

  /** {{{elem \in set}}} */
  def in(elem: TlaEx, set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.in, elem, set)

  /** {{{elem \notin set}}} */
  def notin(elem: TlaEx, set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.notin, elem, set)

  /** {{{left \cap right, left \intersect right}}} */
  def cap(left: TlaEx, right: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.cap, left, right)

  /** {{{left \cup right, left \union right}}} */
  def cup(left: TlaEx, right: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.cup, left, right)

  /** {{{UNION set}}} */
  def union(set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.union, set)

  // Trailing `` in scaladocs prevents auto-format linebreaks
  /**
   * {{{
   * { x \in set: p } }}} ``
   * @param x
   *   must be a variable name
   */
  def filter(x: TlaEx, set: TlaEx, p: TlaEx): TlaEx = {
    BuilderUtil.getBoundVarsOrThrow(x)
    buildBySignatureLookup(TlaSetOper.filter, x, set, p)
  }

  // Trailing `` in scaladocs prevents auto-format linebreaks
  /**
   * {{{
   * { e: pairs[0]._1 \in pairs[0]._2 , ..., pairs[n]._1 \in pairs[n]._2 } }}} ``
   * @param pairs
   *   must be nonempty, and all vars must be unique variable names
   */
  def map(e: TlaEx, pairs: (TlaEx, TlaEx)*): TlaEx = {
    // _mapMixed does all the require checks
    val args = pairs.flatMap { case (k, v) =>
      Seq(k, v)
    }
    mapMixed(e, args: _*)
  }

  // Trailing `` in scaladocs prevents auto-format linebreaks
  /**
   * {{{
   * { e: pairs[0] \in pairs[1] , ..., pairs[n-1] \in pairs[n] } }}} ``
   * @param pairs
   *   must have even, positive arity, and all vars must be unique variable names
   */
  def mapMixed(e: TlaEx, pairs: TlaEx*): TlaEx = {
    // Even, non-zero number of args and every other argument is NameEx
    require(TlaSetOper.map.arity.cond(1 + pairs.size), s"Expected pairs to have even, positive arity, found $pairs.")
    val (vars, _) = TlaOper.deinterleave(pairs)
    val varsMultiseq = vars.flatMap(BuilderUtil.getBoundVarsOrThrow) // any can throw if not the right form
    // Vars must be unique
    val duplicates = varsMultiseq
      .foldLeft(Map.empty[String, Int]) { case (m, s) =>
        m + (s -> (m.getOrElse(s, 0) + 1))
      }
      .filter { case (_, v) => v > 1 }
    require(duplicates.isEmpty, s"Expected vars to be unique, found duplicates: ${duplicates.keySet.mkString(", ")}.")
    buildBySignatureLookup(TlaSetOper.map, e +: pairs: _*)
  }

  /** {{{[fromSet -> toSet]}}} */
  def funSet(fromSet: TlaEx, toSet: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.funSet, fromSet, toSet)

  /**
   * {{{[ kvs[0]._1: kvs[0]._2, ... , kvs[n]._1: kvs[n]._2 ]}}}
   * @param kvs
   *   must be nonempty, and all keys must be unique strings
   */
  def recSet(kvs: (String, TlaEx)*): TlaEx = {
    // _recSetMixed does all the require checks
    val args = kvs.flatMap { case (k, v) =>
      Seq(str(k), v)
    }
    recSetMixed(args: _*)
  }

  /**
   * {{{[ kvs[0]: kvs[1], ... , kvs[n-1]: kvs[n] ]}}}
   * @param kvs
   *   must have even, positive arity, and all keys must be unique strings
   */
  def recSetMixed(kvs: TlaEx*): TlaEx = {
    // All keys must be ValEx(TlaStr(_))
    require(TlaSetOper.recSet.arity.cond(kvs.size), s"Expected kvs to have even, positive arity, found $kvs.")
    val (keys, _) = TlaOper.deinterleave(kvs)
    require(keys.forall {
          case ValEx(_: TlaStr) => true
          case _                => false
        }, s"Expected keys to be TLA+ strings, found $keys.")
    val duplicates = keys.filter(k => keys.count(_ == k) > 1)
    require(duplicates.isEmpty, s"Expected keys to be unique, found duplicates: ${duplicates.mkString(", ")}.")

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
  def seqSet(set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.seqSet, set)

  /** {{{left \subseteq right}}} */
  def subseteq(left: TlaEx, right: TlaEx): TlaEx =
    buildBySignatureLookup(TlaSetOper.subseteq, left, right)

  /** {{{left \ right}}} */
  def setminus(left: TlaEx, right: TlaEx): TlaEx =
    buildBySignatureLookup(TlaSetOper.setminus, left, right)

  /**
   * {{{sets[0] \X sets[1] \X ... \X sets[n]}}}
   * @param sets
   *   must have at least 2 elements
   */
  def times(sets: TlaEx*): TlaEx = {
    require(TlaSetOper.times.arity.cond(sets.size), s"Expected sets to have at least 2 elements, found $sets.")
    buildBySignatureLookup(TlaSetOper.times, sets: _*)
  }

  /** {{{SUBSET set}}} */
  def powSet(set: TlaEx): TlaEx = buildBySignatureLookup(TlaSetOper.powerset, set)
}
