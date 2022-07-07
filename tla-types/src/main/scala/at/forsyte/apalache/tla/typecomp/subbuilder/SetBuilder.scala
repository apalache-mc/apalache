package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeSetBuilder
import scalaz._
import scalaz.Scalaz._

/**
 * Scope-safe builder for TlaSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait SetBuilder extends UnsafeSetBuilder {

  /** {{{{args[0], ..., args[n]} }}} `args` must be nonempty. */
  def enumSet(args: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(args).map { _enumSet(_: _*) }

  /** {{{{} : Set(t)}}} */
  def emptySet(t: TlaType1): TBuilderInstruction = _emptySet(t).point[TBuilderInternalState]

  /** {{{elem \in set}}} */
  def in(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(_in)

  /** {{{elem \notin set}}} */
  def notin(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(_notin)

  /** {{{left \cap right, left \intersect right}}} */
  def cap(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(_cap)

  /** {{{left \cup right, left \union right}}} */
  def cup(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(_cup)

  /** {{{UNION set}}} */
  def union(set: TBuilderInstruction): TBuilderInstruction = set.map(_union)

  /** {{{{ x \in set: p } }}} `x` must be a variable name */
  def filter(x: TBuilderInstruction, set: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionTernary(_filter)(x, set, p)

  /**
   * {{{
   * { e: pairs[0]._1 \in pairs[0]._2 , ..., pairs[n]._1 \in pairs[n]._2 } }}} `pairs` must be nonempty, and all vars
   * must be unique variable names
   */
  def map(e: TBuilderInstruction, pairs: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction =
    boundVarIntroductionVariadic(_map)(e, pairs: _*)

  /**
   * {{{
   * { e: pairs[0] \in pairs[1] , ..., pairs[n-1] \in pairs[n] } }}} `pairs` must have even, positive arity, and all vars
   * must be unique variable names
   */
  def mapMixed(e: TBuilderInstruction, pairs: TBuilderInstruction*): TBuilderInstruction = {
    require(pairs.size % 2 == 0)
    val asPairs = pairs.grouped(2).toSeq.map { case Seq(a, b) =>
      (a, b)
    }
    map(e, asPairs: _*)
  }

  /** {{{[fromSet -> toSet]}}} */
  def funSet(fromSet: TBuilderInstruction, toSet: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(fromSet, toSet)(_funSet)

  /**
   * {{{[ kvs[0]._1: kvs[0]._2, ... , kvs[n]._1: kvs[n]._2 ]}}} `kvs` must be nonempty, and all keys must be unique
   * strings
   */
  def recSet(kvs: (String, TBuilderInstruction)*): TBuilderInstruction =
    for {
      vs <- buildSeq(kvs.map(_._2))
      ks = kvs.map(_._1)
    } yield _recSet(ks.zip(vs): _*)

  /**
   * {{{[ kvs[0]: kvs[1], ... , kvs[n-1]: kvs[n] ]}}} `kvs` must have even, positive arity, and all keys must be unique
   * strings
   */
  def recSetMixed(kvs: TBuilderInstruction*): TBuilderInstruction = buildSeq(kvs).map { _recSetMixed(_: _*) }

  /** {{{Seq(set)}}} */
  def seqSet(set: TBuilderInstruction): TBuilderInstruction = set.map(_seqSet)

  /** {{{left \subseteq right}}} */
  def subseteq(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(_subseteq)

  /** {{{left \ right}}} */
  def setminus(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(_setminus)

  /** {{{sets[0] \X sets[1] \X ... \X sets[n]}}} `sets` must have at least 2 elements */
  def times(sets: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(sets).map { _times(_: _*) }

  /** {{{SUBSET set}}} */
  def powSet(set: TBuilderInstruction): TBuilderInstruction = set.map(_powSet)
}
