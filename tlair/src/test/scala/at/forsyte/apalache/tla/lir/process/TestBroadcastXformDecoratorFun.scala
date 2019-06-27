package at.forsyte.apalache.tla.lir.process

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.TransformationListener
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, ValEx}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
  * Test transformation decorators.
  */
@RunWith(classOf[JUnitRunner])
class TestBroadcastXformDecoratorFun extends FunSuite {
  test("test apply") {
    // our listener just changes the flag
    var changed = false
    val listener = new TransformationListener {
      override def onTransformation(originalEx: TlaEx, newEx: TlaEx): Unit = { changed = true }
    }

    // this simple transformer is always returning 2
    def xformer(e: TlaEx) = ValEx(TlaInt(2))

    // create the decorator
    val decorator = new BroadcastXformDecoratorFun(List(listener), xformer)
    // use the decorator as a normal function
    val output = decorator(ValEx(TlaInt(1)))
    assert(output == ValEx(TlaInt(2)))
    assert(changed)
  }

  test("test recursive decorators") {
    // our listener just changes the flag
    var changes = 0
    val listener = new TransformationListener {
      override def onTransformation(originalEx: TlaEx, newEx: TlaEx): Unit = { changes += 1 }
    }

    // create a factory that can be used multiple times by the user, in order to decorate multiple functions
    val factory = new BroadcastXformDecoratorFactory()
    factory.listeners +:= listener

    // a recursive transformer whose every call should be decorated
    def xformer: TlaEx => TlaEx = factory.decorate {
      case ValEx(_) =>
        ValEx(TlaInt(2))

      case OperEx(oper, args@_*) =>
        OperEx(oper, args map xformer: _*)

      case e => e
    }

    // use the decorated recursive function
    val output = xformer(tla.plus(tla.int(1), tla.int(3)))
    assert(output == tla.plus(tla.int(2), tla.int(2)))
    assert(changes == 3)
  }
}
