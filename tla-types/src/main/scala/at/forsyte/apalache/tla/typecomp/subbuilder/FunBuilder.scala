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

  //////////////////
  // APP sepcific //
  //////////////////

//  /** f[e] for {{{f: a -> b}}} */
//  def appFun(f: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(f, e)(_appFun)
//
//  /** tup[i] for {{{tup: <<t1, ..., tn>>, i \in 1..n}}} */
//  def appTup(tup: TBuilderInstruction, i: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(tup, i)(_appTup)
//
//  /** r.x for {{{r: [a1: v1, ..., an: vn], x \in {"a1", ..., "an"} }}}} */
//  def appRec(r: TBuilderInstruction, x: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(r, x)(_appRec)
//
//  /** s[i] for {{{s: Seq(t)}}}} */
//  def appSeq(s: TBuilderInstruction, i: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(s, i)(_appSeq)

  /////////////////////
  // DOMAIN overload //
  /////////////////////

  def dom(f: TBuilderInstruction): TBuilderInstruction = f.map { _dom }

  /////////////////////
  // DOMAIN sepcific //
  /////////////////////

//  /** DOMAIN f for {{{f: a -> b}}} */
//  def domFun(f: TBuilderInstruction): TBuilderInstruction = f.map { _domFun }
//
//  /** DOMAIN tup for {{{tup: <<t1,...,tn>>}}} */
//  def domTup(tup: TBuilderInstruction): TBuilderInstruction = tup.map { _domTup }
//
//  /** DOMAIN r for {{{r: [a1: v1, ..., an: vn]}}} */
//  def domRec(r: TBuilderInstruction): TBuilderInstruction = r.map { _domRec }
//
//  /** DOMAIN s for {{{s: Seq(t)}}} */
//  def domSeq(s: TBuilderInstruction): TBuilderInstruction = s.map { _domSeq }

  /////////////////////
  // EXCEPT overload //
  /////////////////////

  /** [f EXCEPT !.x = e] for any Applicative f */
  def except(f: TBuilderInstruction, x: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(f, x, e)(_except)

  /////////////////////
  // EXCEPT specific //
  /////////////////////
//
//  /** [f EXCEPT ![x] = e] for {{{f: a -> b}}} */
//  def exceptFun(f: TBuilderInstruction, x: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction =
//    ternaryFromUnsafe(f, x, e)(_exceptFun)
//
//  /** [tup EXCEPT ![i] = e] for {{{tup: <<t1, ..., tn>>, i \in 1..n}}} */
//  def exceptTup(tup: TBuilderInstruction, i: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction =
//    ternaryFromUnsafe(tup, i, e)(_exceptTup)
//
//  /** [r EXCEPT !.x = e] for {{{r: [a1: v1, ..., an: vn], x \in {"a1", ..., "an"} }}}} */
//  def exceptRec(r: TBuilderInstruction, x: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction =
//    ternaryFromUnsafe(r, x, e)(_exceptRec)
//
//  /** [s EXCEPT ![i] = e] for {{{s: Seq(t)}}}} */
//  def exceptSeq(s: TBuilderInstruction, i: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction =
//    ternaryFromUnsafe(s, i, e)(_exceptSeq)
}
