package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.lir.TlaType1
import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeFunBuilder
import scalaz._
import scalaz.Scalaz._

/**
 * Type-safe builder for TlaFunOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait FunBuilder extends UnsafeFunBuilder {

  /**
   * Record constructor [ k1 |-> v1, ... , kN |-> vN ]; must have at least 1 key-value pair and all keys must be unique
   */
  def rec(args: (String, TBuilderInstruction)*): TBuilderInstruction = for {
    vs <- buildSeq(args.map(_._2))
    ks = args.map(_._1)
  } yield _rec(ks.zip(vs): _*)

  /**
   * Alternate call method, where pairs are passed interleaved.
   *
   * @see
   *   rec[[rec(args: (String, TBuilderInstruction)*)]]
   */
  def recMixed(args: TBuilderInstruction*): TBuilderInstruction =
    buildSeq(args).map { _recMixed(_: _*) }

  /** {{{<<t1, ..., tn>>}}} with a tuple-type */
  def tuple(args: TBuilderInstruction*): TBuilderInstruction = buildSeq(args).map(_tuple(_: _*))

  /** {{{<<>>}}} with a sequence type */
  def emptySeq(t: TlaType1): TBuilderInstruction = _emptySeq(t).point[TBuilderInternalState]

  /** {{{<<t1, ..., tn>>}}} with a sequence-type. Must be nonempty. */
  def seq(args: TBuilderInstruction*): TBuilderInstruction = buildSeq(args).map { _seq }

  /** [x \in S |-> e] */
  def funDef(e: TBuilderInstruction, x: TBuilderInstruction, S: TBuilderInstruction): TBuilderInstruction = for {
    eEx <- e
    xEx <- x
    setEx <- S
    _ <- markAsBound(xEx)
  } yield _funDef(eEx, xEx, setEx)

  //////////////////
  // APP overload //
  //////////////////

  /** f[x] for any Applicative f */
  def app(f: TBuilderInstruction, x: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(f, x)(_app)

  /////////////////////
  // DOMAIN overload //
  /////////////////////

  def dom(f: TBuilderInstruction): TBuilderInstruction = f.map { _dom }

  /////////////////////
  // EXCEPT overload //
  /////////////////////

  /** [f EXCEPT !.x = e] for any Applicative f */
  def except(f: TBuilderInstruction, x: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(f, x, e)(_except)

}
