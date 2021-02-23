package at.forsyte.apalache.tla.lir.storage

import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestChangeListener extends FunSuite with BeforeAndAfterEach {
  private var listener = new ChangeListener

  override protected def beforeEach(): Unit = {
    listener = new ChangeListener
  }

  test("track 'x' to 'y'") {
    val x = NameEx("x")
    val y = NameEx("y")
    listener.onTransformation(x, y)
    assert(x.ID == listener.traceBack(y.ID))
  }

  test("track {'x'} to {'y'}") {
    val x = NameEx("x")
    val y = NameEx("y")
    listener.onTransformation(x, y)
    val setOfX = tla.enumSet(x)
    val setOfY = tla.enumSet(y)
    listener.onTransformation(setOfX, setOfY)

    assert(setOfX.ID == listener.traceBack(setOfY.ID))
    // the expressions inside the sets are not affected by the set transformation
    assert(x.ID == listener.traceBack(y.ID))
  }

  test("track {'x'} to {'y'} without 'x' to 'y'") {
    val x = NameEx("x")
    val y = NameEx("y")
    val setOfX = tla.enumSet(x)
    val setOfY = tla.enumSet(y)
    // in this case, we only know that setOfX was transformed to setOfY,
    // but we do not know that x was transformed to y
    listener.onTransformation(setOfX, setOfY)

    assert(setOfX.ID == listener.traceBack(setOfY.ID))
    // as a result, the origin of y is the origin id of the smallest expression that contains y and has the source info,
    // that is, the id of setOfX
    assert(setOfX.ID == listener.traceBack(y.ID))
  }

  test("track {{'x'}} to {{'y'}} without {'x'} to {'y'} but 'x' to 'y'") {
    val x = NameEx("x")
    val y = NameEx("y")
    val setOfX = tla.enumSet(x)
    val setOfSetOfX = tla.enumSet(setOfX)
    val setOfY = tla.enumSet(y)
    val setOfSetOfY = tla.enumSet(setOfY)
    // we know that x was transformed to y
    listener.onTransformation(x, y)
    // we also know that setOfSetOfX was transformed to setOfSetOfY,
    // but we do not know that setOfX was transformed to setOfY
    listener.onTransformation(setOfSetOfX, setOfSetOfY)

    assert(setOfSetOfX.ID == listener.traceBack(setOfSetOfY.ID))
    // as a result, the origin of y is the origin id of the smallest expression
    // that contains setOfY and has the source info,
    // that is, the id of setOfSetOfX
    assert(setOfSetOfX.ID == listener.traceBack(setOfY.ID))
    // however, we should know that y was produced from x
    assert(x.ID == listener.traceBack(y.ID))
  }
}
