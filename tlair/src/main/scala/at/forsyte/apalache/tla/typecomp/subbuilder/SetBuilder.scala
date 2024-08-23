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
trait SetBuilder {
  private val unsafeBuilder = new UnsafeSetBuilder {}

  /**
   * {{{
   * {args[0], ..., args[n]} }}} To construct empty sets, use [[emptySet]] instead.
   * @param args
   *   must be nonempty.
   */
  def enumSet(args: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(args).map { unsafeBuilder.enumSet(_: _*) }

  /** {{{{} : Set(t)}}} */
  def emptySet(t: TlaType1): TBuilderInstruction = unsafeBuilder.emptySet(t).point[TBuilderInternalState]

  /** {{{elem \in set}}} */
  def in(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(unsafeBuilder.in)

  /** {{{elem \notin set}}} */
  def notin(elem: TBuilderInstruction, set: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(elem, set)(unsafeBuilder.notin)

  /** {{{left \cap right, left \intersect right}}} */
  def cap(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(unsafeBuilder.cap)

  /** {{{left \cup right, left \union right}}} */
  def cup(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(unsafeBuilder.cup)

  /** {{{UNION set}}} */
  def union(set: TBuilderInstruction): TBuilderInstruction = set.map(unsafeBuilder.union)

  // Trailing `` in scaladocs prevents auto-format linebreaks
  /**
   * {{{
   * { x \in set: p } }}} ``
   * @param x
   *   must be a variable name
   */
  def filter(x: TBuilderInstruction, set: TBuilderInstruction, p: TBuilderInstruction): TBuilderInstruction =
    boundVarIntroductionTernary(unsafeBuilder.filter)(x, set, p)

  // Trailing `` in scaladocs prevents auto-format linebreaks
  /**
   * {{{
   * { e: pairs[0]._1 \in pairs[0]._2 , ..., pairs[n]._1 \in pairs[n]._2 } }}} ``
   * @param pairs
   *   must be nonempty, and all vars must be unique variable names
   */
  def map(e: TBuilderInstruction, pairs: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction =
    boundVarIntroductionVariadic(unsafeBuilder.map)(e, pairs: _*)

  // Trailing `` in scaladocs prevents auto-format linebreaks
  /**
   * {{{
   * { e: pairs[0] \in pairs[1] , ..., pairs[n-1] \in pairs[n] } }}} ``
   * @param pairs
   *   must have even, positive arity, and all vars must be unique variable names
   */
  def mapMixed(e: TBuilderInstruction, pairs: TBuilderInstruction*): TBuilderInstruction = {
    require(pairs.size % 2 == 0, s"Expected pairs to have even arity, found $pairs.")
    val asPairs = pairs.grouped(2).toSeq.map { case Seq(a, b) =>
      (a, b)
    }
    map(e, asPairs: _*)
  }

  /** {{{[fromSet -> toSet]}}} */
  def funSet(fromSet: TBuilderInstruction, toSet: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(fromSet, toSet)(unsafeBuilder.funSet)

  /**
   * {{{[ kvs[0]._1: kvs[0]._2, ... , kvs[n]._1: kvs[n]._2 ]}}}
   * @param kvs
   *   must be nonempty, and all keys must be unique strings
   */
  def recSet(kvs: (String, TBuilderInstruction)*): TBuilderInstruction =
    for {
      vs <- buildSeq(kvs.map(_._2))
      ks = kvs.map(_._1)
    } yield unsafeBuilder.recSet(ks.zip(vs): _*)

  /**
   * {{{[ kvs[0]: kvs[1], ... , kvs[n-1]: kvs[n] ]}}}
   * @param kvs
   *   must have even, positive arity, and all keys must be unique strings
   */
  def recSetMixed(kvs: TBuilderInstruction*): TBuilderInstruction = buildSeq(kvs).map {
    unsafeBuilder.recSetMixed(_: _*)
  }

  /** {{{Seq(set)}}} */
  def seqSet(set: TBuilderInstruction): TBuilderInstruction = set.map(unsafeBuilder.seqSet)

  /** {{{left \subseteq right}}} */
  def subseteq(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(unsafeBuilder.subseteq)

  /** {{{left \ right}}} */
  def setminus(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(left, right)(unsafeBuilder.setminus)

  /**
   * {{{sets[0] \X sets[1] \X ... \X sets[n]}}}
   * @param sets
   *   must have at least 2 elements
   */
  def times(sets: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(sets).map { unsafeBuilder.times(_: _*) }

  /** {{{SUBSET set}}} */
  def powSet(set: TBuilderInstruction): TBuilderInstruction = set.map(unsafeBuilder.powSet)
}
