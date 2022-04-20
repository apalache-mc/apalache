package at.forsyte.apalache.tla.typecmp.subbuilder

import at.forsyte.apalache.tla.typecmp.raw.RawBoolBuilder
import at.forsyte.apalache.tla.typecmp.{BuilderWrapper, NameWrapper}
import scalaz._

/**
 * Builder for TlaBoolOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait BoolBuilder extends RawBoolBuilder {

  import at.forsyte.apalache.tla.typecmp.BuilderUtil._

  def and(argsW: BuilderWrapper*): BuilderWrapper = polyadicFromRaw(argsW)(_and(_: _*))

  def or(argsW: BuilderWrapper*): BuilderWrapper = polyadicFromRaw(argsW)(_or(_: _*))

  def not(pW: BuilderWrapper): BuilderWrapper = pW.map(_not)

  def impl(pW: BuilderWrapper, qW: BuilderWrapper): BuilderWrapper = binaryFromRaw(pW, qW)(_impl)

  def equiv(pW: BuilderWrapper, qW: BuilderWrapper): BuilderWrapper = binaryFromRaw(pW, qW)(_equiv)

  def forall(elemW: NameWrapper, setW: BuilderWrapper, predW: BuilderWrapper): BuilderWrapper = for {
    elem <- elemW
    set <- setW
    pred <- predW
    _ <- markAsBound(elem)
  } yield _forall(elem, set, pred)

  def forall(elemW: NameWrapper, predW: BuilderWrapper): BuilderWrapper = for {
    elem <- elemW
    pred <- predW
    _ <- markAsBound(elem)
  } yield _forall(elem, pred)

  def exists(elemW: NameWrapper, setW: BuilderWrapper, predW: BuilderWrapper): BuilderWrapper = for {
    elem <- elemW
    set <- setW
    pred <- predW
    _ <- markAsBound(elem)
  } yield _exists(elem, set, pred)

  def exists(elemW: NameWrapper, predW: BuilderWrapper): BuilderWrapper = for {
    elem <- elemW
    pred <- predW
    _ <- markAsBound(elem)
  } yield _exists(elem, pred)

}
