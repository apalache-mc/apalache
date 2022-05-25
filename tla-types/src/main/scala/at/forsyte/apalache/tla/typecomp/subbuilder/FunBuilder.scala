package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.BuilderUtil._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeFunBuilder
import scalaz._

/**
 * Type-safe builder for TlaFunOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait FunBuilder extends UnsafeFunBuilder {

  /** {{{(t1, ..., tn) => <<t1, ..., tn>>}}} */
  def tuple(args: TBuilderInstruction*): TBuilderInstruction = buildSeq(args).map(_tuple(_: _*))

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
