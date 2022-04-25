package at.forsyte.apalache.tla.typecmp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecmp.BuilderUtil._
import at.forsyte.apalache.tla.typecmp.{BuilderWrapper, InternalState, NameWrapper, ValWrapper}
import at.forsyte.apalache.tla.typecmp.raw.RawSetBuilder
import scalaz._
import scalaz.Scalaz._

/**
 * Builder for TlaSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait SetBuilder extends RawSetBuilder {

  /** {x1, ..., xn}, must have >0 args. */
  def enumSet(argW: BuilderWrapper, argsW: BuilderWrapper*): BuilderWrapper = for {
    argEx <- argW
    argsExs <- buildSeq(argsW)
  } yield _enumSet(argEx, argsExs: _*)

  /** {}: Set(elemType) */
  def emptySet(elemType: TlaType1): BuilderWrapper = _emptySet(elemType).point[InternalState]

  /** elem \in set */
  def in(elemW: BuilderWrapper, setW: BuilderWrapper): BuilderWrapper =
    binaryFromRaw(elemW, setW)(_in)

  /** elem \notin set */
  def notin(elemW: BuilderWrapper, setW: BuilderWrapper): BuilderWrapper =
    binaryFromRaw(elemW, setW)(_notin)

  /** left \cap right, left \intersect right */
  def cap(leftW: BuilderWrapper, rightW: BuilderWrapper): BuilderWrapper =
    binaryFromRaw(leftW, rightW)(_cap)

  /** left \cup right, left `\`union right */
  def cup(leftW: BuilderWrapper, rightW: BuilderWrapper): BuilderWrapper =
    binaryFromRaw(leftW, rightW)(_cup)

  /** UNION set */
  def union(setW: BuilderWrapper): BuilderWrapper = setW.map(_union)

  /** { x \in set: p } */
  def filter(xW: NameWrapper, setW: BuilderWrapper, pW: BuilderWrapper): BuilderWrapper = for {
    x <- xW
    set <- setW
    p <- pW
    _ <- markAsBound(x)
  } yield _filter(x, set, p)

  /** { mapExpr: x1 \in set1 , ..., xN \in setN }, must have at least 1 var-set pair */
  def map(
      eW: BuilderWrapper,
      x1W: NameWrapper,
      set1W: BuilderWrapper,
      pairsW: BuilderWrapper*): BuilderWrapper = for {
    x1 <- x1W
    set1 <- set1W
    // Even # of args for deinterleave
    _ = require(pairsW.size % 2 == 0)
    pairs <- buildSeq(pairsW)
    (xs, _) = TlaOper.deinterleave(pairs)
    // every other argument is NameEx
    _ = require(xs.forall { _.isInstanceOf[NameEx] })
    mapExpr <- eW
    // Mark x1 and all vars as bound
    _ <- xs.map(_.asInstanceOf[NameEx]).foldLeft(markAsBound(x1)) { case (cmp, xi) =>
      cmp.flatMap({ _ => markAsBound(xi) })
    }
  } yield _map(mapExpr, x1, set1, pairs: _*)

  /** Function set constructor [fromSet -> toSet] */
  def funSet(fromSetW: BuilderWrapper, toSetW: BuilderWrapper): BuilderWrapper =
    binaryFromRaw(fromSetW, toSetW)(_funSet)

  /** Record set constructor [ k1: v1, ... , kN: vN ], must have at least 1 key-value pair */
  def recSet(k1W: ValWrapper, v1W: BuilderWrapper, kvsW: BuilderWrapper*): BuilderWrapper = for {
    k1 <- k1W
    v1 <- v1W
    kvs <- buildSeq(kvsW)
  } yield _recSet(k1, v1, kvs: _*)

  /**
   * Alternate call method, where Scala strings are passed in place of ValWrappers
   * @see
   *   recSet[[recSet(k1W: ValWrapper, v1W: BuilderWrapper, kvsW: BuilderWrapper*)]]
   */
  def recSet(kv1W: (String, BuilderWrapper), kvsW: (String, BuilderWrapper)*): BuilderWrapper = for {
    v1 <- kv1W._2
    k1 = kv1W._1
    ks = kvsW.map(_._1)
    vs <- buildSeq(kvsW.map(_._2))
  } yield _recSet(k1 -> v1, ks.zip(vs): _*)

  /** Seq(set) */
  def seqSet(setW: BuilderWrapper): BuilderWrapper = setW.map(_seqSet)

  /** left \subseteq right */
  def subseteq(leftW: BuilderWrapper, rightW: BuilderWrapper): BuilderWrapper = binaryFromRaw(leftW, rightW)(_subseteq)

  /** left \ right */
  def setminus(leftW: BuilderWrapper, rightW: BuilderWrapper): BuilderWrapper = binaryFromRaw(leftW, rightW)(_setminus)

  /** s1 \X s2 \X ... */
  def times(s1W: BuilderWrapper, s2W: BuilderWrapper, setsW: BuilderWrapper*): BuilderWrapper = for {
    s1 <- s1W
    s2 <- s2W
    sets <- buildSeq(setsW)
  } yield _times(s1, s2, sets: _*)

  /** SUBSET set */
  def powSet(setW: BuilderWrapper): BuilderWrapper = setW.map(_powSet)
}
