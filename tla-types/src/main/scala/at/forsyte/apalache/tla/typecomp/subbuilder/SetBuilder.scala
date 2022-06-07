package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeSetBuilder
import scalaz._
import scalaz.Scalaz._

/**
 * Type-safe builder for TlaSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait SetBuilder extends UnsafeSetBuilder {

  /** {args[0], ..., args[n]}, must have >0 args. */
  def enumSet(args: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(args).map { _enumSet(_: _*) }

  /** {}: Set(elemType) */
  def emptySet(elemType: TlaType1): TBuilderInstruction = _emptySet(elemType).point[TBuilderInternalState]

  /** elem \in set */
  def in(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(_in)

  /** elem \notin set */
  def notin(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(_notin)

  /** left \cap right, left \intersect right */
  def cap(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(_cap)

  /** left \cup right, left `\`union right */
  def cup(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(_cup)

  /** UNION set */
  def union(set: TBuilderInstruction): TBuilderInstruction = set.map(_union)

  /** { x \in set: p } */
  def filter(x: TBuilderInstruction, set: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    for {
      xEx <- x
      setEx <- set
      pEx <- p
      _ <- markAsBound(xEx)
    } yield _filter(xEx, setEx, pEx)

  /** { mapExpr: x1 \in set1 , ..., xN \in setN }, must have at least 1 var-set pair */
  def map(
      e: TBuilderInstruction,
      varSetPairs: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction = {
    val args = varSetPairs.flatMap { case (k, v) =>
      Seq(k, v)
    }
    mapMixed(e, args: _*)
  }

  /**
   * Alternate call method, where pairs are passed interleaved
   *
   * @see
   *   map[[mapMixed(e: TBuilderInstruction, varSetPairs: (TBuilderInstruction, TBuilderInstruction)*)]]
   */
  def mapMixed(
      e: TBuilderInstruction,
      varSetPairs: TBuilderInstruction*): TBuilderInstruction = {
    // Requirements for deinterleave
    require(varSetPairs.nonEmpty)
    require(varSetPairs.size % 2 == 0)
    for {
      pairs <- buildSeq(varSetPairs)
      (xs, _) = TlaOper.deinterleave(pairs)
      // every other argument is NameEx
      _ = require(xs.forall {
        _.isInstanceOf[NameEx]
      })
      mapExpr <- e
      // Mark all vars as bound
      _ <- xs.map(_.asInstanceOf[NameEx]).foldLeft(().point[TBuilderInternalState]) { case (cmp, xi) =>
        cmp.flatMap { _ => markAsBound(xi) }
      }
    } yield _mapMixed(mapExpr, pairs: _*)
  }

  /** Function set constructor [fromSet -> toSet] */
  def funSet(fromSet: TBuilderInstruction, toSet: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(fromSet, toSet)(_funSet)

  /** Record set constructor [ k1: v1, ... , kN: vN ], must have at least 1 key-value pair */
  def recSet(kvs: (String, TBuilderInstruction)*): TBuilderInstruction =
    for {
      vs <- buildSeq(kvs.map(_._2))
      ks = kvs.map(_._1)
    } yield _recSet(ks.zip(vs): _*)

  /**
   * Alternate call method, where pairs are passed interleaved.
   *
   * @see
   *   recSet[[recSet(kvs: (String, TBuilderInstruction)*)]]
   */
  def recSetMixed(kvs: TBuilderInstruction*): TBuilderInstruction = buildSeq(kvs).map { _recSetMixed(_: _*) }

  /** Seq(set) */
  def seqSet(set: TBuilderInstruction): TBuilderInstruction = set.map(_seqSet)

  /** left \subseteq right */
  def subseteq(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(_subseteq)

  /** left \ right */
  def setminus(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(_setminus)

  /** s1 \X s2 \X ... , must have >= 2 args */
  def times(sets: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(sets).map { _times(_: _*) }

  /** SUBSET set */
  def powSet(set: TBuilderInstruction): TBuilderInstruction = set.map(_powSet)
}
