package at.forsyte.apalache.tla.typecmp.subbuilder

import at.forsyte.apalache.tla.typecmp.raw.RawBoolBuilder
import at.forsyte.apalache.tla.typecmp.{BuilderWrapper, NameWrapper}
import at.forsyte.apalache.tla.typecmp.BuilderUtil._

/**
 * Builder for TlaBoolOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait BoolBuilder extends RawBoolBuilder {

  /** /\_{i=1}^n args */
  def and(argsW: BuilderWrapper*): BuilderWrapper = buildSeq(argsW).map(_and(_: _*))

  /** \/_{i=1}^n args */
  def or(argsW: BuilderWrapper*): BuilderWrapper = buildSeq(argsW).map(_or(_: _*))

  /** ~p */
  def not(pW: BuilderWrapper): BuilderWrapper = pW.map(_not)

  /** p => q */
  def impl(pW: BuilderWrapper, qW: BuilderWrapper): BuilderWrapper = binaryFromRaw(pW, qW)(_impl)

  /** p <=> q */
  def equiv(pW: BuilderWrapper, qW: BuilderWrapper): BuilderWrapper = binaryFromRaw(pW, qW)(_equiv)

  /** \A elem \in set: pred */
  def forall(xW: NameWrapper, setW: BuilderWrapper, pW: BuilderWrapper): BuilderWrapper = for {
    x <- xW
    set <- setW
    p <- pW
    _ <- markAsBound(x)
  } yield _forall(x, set, p)

  /** \A elem: pred */
  def forall(xW: NameWrapper, pW: BuilderWrapper): BuilderWrapper = for {
    x <- xW
    p <- pW
    _ <- markAsBound(x)
  } yield _forall(x, p)

  /** \E elem \in set: pred */
  def exists(xW: NameWrapper, setW: BuilderWrapper, pW: BuilderWrapper): BuilderWrapper = for {
    x <- xW
    set <- setW
    p <- pW
    _ <- markAsBound(x)
  } yield _exists(x, set, p)

  /** \E elem: pred */
  def exists(xW: NameWrapper, pW: BuilderWrapper): BuilderWrapper = for {
    x <- xW
    p <- pW
    _ <- markAsBound(x)
  } yield _exists(x, p)

}
