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
    boundVarIntroductionTernary(_filter)(x, set, p)

  /** { mapExpr: x1 \in set1 , ..., xN \in setN }, must have at least 1 var-set pair */
  def map(
      e: TBuilderInstruction,
      varSetPairs: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction = {
    for {
      mapExpr <- e
      boundAfterMapExpr <- allBound // xi may not appear as bound in mapExpr
      _ = {}
      pairs <- varSetPairs.foldLeft(Seq.empty[(TlaEx, TlaEx)].point[TBuilderInternalState]) {
        case (cmp, (variable, set)) =>
          for {
            seq <- cmp
            setEx <- set
            usedInS <- allUsed // xi may not appear as bound or free in S
            xEx <- variable
            _ = require(xEx.isInstanceOf[NameEx])
            _ <- markAsBound(xEx)
            // x is shadowed iff boundAfterX \subseteq usedInS \union boundAfrerP
            boundAfterX <- allBound
            diff = (boundAfterX -- usedInS) -- boundAfterMapExpr
          } yield
            if (diff.isEmpty) {
              val name = xEx.asInstanceOf[NameEx].name // require would have already thrown if not NameEx
              throw new TBuilderScopeException(s"Variable $name is shadowed in $mapExpr or $setEx.")
            } else seq :+ (xEx, setEx)
      }
    } yield _map(mapExpr, pairs: _*)
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
    require(varSetPairs.size % 2 == 0)
    val asPairs = varSetPairs.grouped(2).toSeq.map { case Seq(a, b) =>
      (a, b)
    }
    map(e, asPairs: _*)
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
