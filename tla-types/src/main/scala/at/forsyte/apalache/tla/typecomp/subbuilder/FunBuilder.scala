package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir.TlaType1
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp.{TBuilderInstruction, TBuilderInternalState}
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeFunBuilder
import scalaz._
import scalaz.Scalaz._

/**
 * Scope-safe builder for TlaFunOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait FunBuilder {
  private val unsafeBuilder = new UnsafeFunBuilder

  /**
   * {{{[ args[0]._1 |-> args[0]._2, ..., args[n]._1 |-> args[n]._2 ]}}}
   * @param args
   *   must be nonempty, and all keys must be unique strings
   */
  def rec(args: (String, TBuilderInstruction)*): TBuilderInstruction = for {
    vs <- buildSeq(args.map(_._2))
    ks = args.map(_._1)
  } yield unsafeBuilder.rec(ks.zip(vs): _*)

  /**
   * {{{[ args[0] |-> args[1], ..., args[n-1] |-> args[n] ]}}}
   * @param args
   *   must have even, positive arity, and all keys must be unique strings
   */
  def recMixed(args: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(args).map { unsafeBuilder.recMixed(_: _*) }

  /** {{{<<args[0], ..., args[n]>> : <<t1, ..., tn>>}}} */
  def tuple(args: TBuilderInstruction*): TBuilderInstruction = buildSeq(args).map(unsafeBuilder.tuple(_: _*))

  /** {{{<<>> : Seq(t)}}} */
  def emptySeq(t: TlaType1): TBuilderInstruction = unsafeBuilder.emptySeq(t).point[TBuilderInternalState]

  /**
   * {{{<<args[0], ..., args[n]>> : Seq(t)}}}
   * @param args
   *   must be nonempty.
   */
  def seq(args: TBuilderInstruction*): TBuilderInstruction = buildSeq(args).map { unsafeBuilder.seq }

  /**
   * {{{[pairs[0]._1 \in pairs[0]._2, ..., pairs[n]._1 \in pairs[n]._2 |-> e]}}}
   * @param pairs
   *   must be nonempty, and all vars must be unique variable names
   */
  def funDef(e: TBuilderInstruction, pairs: (TBuilderInstruction, TBuilderInstruction)*): TBuilderInstruction =
    boundVarIntroductionVariadic(unsafeBuilder.funDef)(e, pairs: _*)

  /**
   * {{{[pairs[0] \in pairs[1], ..., pairs[n-1] \in pairs[n] |-> e]}}}
   * @param pairs
   *   must have even, positive arity, and all vars must be unique variable names
   */
  def funDefMixed(e: TBuilderInstruction, pairs: TBuilderInstruction*): TBuilderInstruction = {
    require(pairs.size % 2 == 0, s"Expected pairs to have even arity, found $pairs.")
    val asPairs = pairs.grouped(2).toSeq.map { case Seq(a, b) =>
      (a, b)
    }
    funDef(e, asPairs: _*)
  }

  //////////////////
  // APP overload //
  //////////////////

  /**
   * {{{f[x]}}}
   * @param f
   *   must be [[Applicative]]
   */
  def app(f: TBuilderInstruction, x: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(f, x)(unsafeBuilder.app)

  /////////////////////
  // DOMAIN overload //
  /////////////////////

  /**
   * {{{DOMAIN f}}}
   * @param f
   *   must be [[Applicative]]
   */
  def dom(f: TBuilderInstruction): TBuilderInstruction = f.map { unsafeBuilder.dom }

  /////////////////////
  // EXCEPT overload //
  /////////////////////

  /**
   * {{{[f EXCEPT ![x] = e]}}}
   * @param f
   *   must be [[Applicative]]
   */
  def except(f: TBuilderInstruction, x: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(f, x, e)(unsafeBuilder.except)

}
