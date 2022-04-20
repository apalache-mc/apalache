package at.forsyte.apalache.tla.typecmp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecmp.BuilderUtil._
import at.forsyte.apalache.tla.typecmp.{BuilderWrapper, InternalState, NameWrapper}
import at.forsyte.apalache.tla.typecmp.raw.RawSetBuilder
import scalaz._
import scalaz.Scalaz._

/**
 * @author
 *   Jure Kukovec
 */
trait SetBuilder extends RawSetBuilder {
  def enumSet(argW: BuilderWrapper, argsW: BuilderWrapper*): BuilderWrapper = for {
    argEx <- argW
    argsExs <- buildSeq(argsW)
  } yield _enumSet(argEx, argsExs: _*)

  def emptySet(elemType: TlaType1): BuilderWrapper = _emptySet(elemType).point[InternalState]

  def in(elemW: BuilderWrapper, setW: BuilderWrapper): BuilderWrapper =
    binaryFromRaw(elemW, setW)(_in)

  def notin(elemW: BuilderWrapper, setW: BuilderWrapper): BuilderWrapper =
    binaryFromRaw(elemW, setW)(_notin)

  def cap(leftW: BuilderWrapper, rightW: BuilderWrapper): BuilderWrapper =
    binaryFromRaw(leftW, rightW)(_cap)

  def cup(leftW: BuilderWrapper, rightW: BuilderWrapper): BuilderWrapper =
    binaryFromRaw(leftW, rightW)(_cup)

  def union(setW: BuilderWrapper): BuilderWrapper = setW.map(_union)

  def filter(xW: NameWrapper, setW: BuilderWrapper, pW: BuilderWrapper): BuilderWrapper = for {
    x <- xW
    set <- setW
    p <- pW
    _ <- markAsBound(x)
  } yield _filter(x, set, p)

  def map(
      mapExprW: BuilderWrapper,
      var1W: NameWrapper,
      set1W: BuilderWrapper,
      varsAndSetsInterleavedW: BuilderWrapper*): BuilderWrapper = for {
    var1 <- var1W
    set1 <- set1W
    varsAndSetsInterleaved <- buildSeq(varsAndSetsInterleavedW)
    (vars, _) = TlaOper.deinterleave(varsAndSetsInterleaved)
    _ = require(vars.forall { _.isInstanceOf[NameEx] })
    mapExpr <- mapExprW
    // Mark v1 and all vars as bound
    _ <- vars.map(_.asInstanceOf[NameEx]).foldLeft(markAsBound(var1)) { case (cmp, v) =>
      cmp.flatMap({ _ => markAsBound(v) })
    }
  } yield _map(mapExpr, var1, set1, varsAndSetsInterleaved: _*)

  def funSet(fromSetW: BuilderWrapper, toSetW: BuilderWrapper): BuilderWrapper =
    binaryFromRaw(fromSetW, toSetW)(_funSet)

  def recSet(kv1W: (String, BuilderWrapper), kvsW: (String, BuilderWrapper)*): BuilderWrapper = for {
    v1 <- kv1W._2
    k1 = kv1W._1
    vs <- buildSeq(kvsW.map(_._2))
    ks = kvsW.map(_._1)
  } yield _recSet((k1, v1), ks.zip(vs): _*)

  def seqSet(setW: BuilderWrapper): BuilderWrapper = setW.map(_seqSet)

  def subseteq(leftW: BuilderWrapper, rightW: BuilderWrapper): BuilderWrapper = binaryFromRaw(leftW, rightW)(_subseteq)

  def setminus(leftW: BuilderWrapper, rightW: BuilderWrapper): BuilderWrapper =
    binaryFromRaw(leftW, rightW)(_setminus)

  def times(s1W: BuilderWrapper, s2W: BuilderWrapper, setsW: BuilderWrapper*): BuilderWrapper = for {
    s1 <- s1W
    s2 <- s2W
    sets <- buildSeq(setsW)
  } yield _times(s1, s2, sets: _*)

  def powSet(setW: BuilderWrapper): BuilderWrapper = setW.map(_powSet)
}
