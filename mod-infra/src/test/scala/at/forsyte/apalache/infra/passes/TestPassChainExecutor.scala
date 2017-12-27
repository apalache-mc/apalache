package at.forsyte.apalache.infra.passes

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.easymock.EasyMockSugar
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestPassChainExecutor extends FunSuite with EasyMockSugar {
  test("""2 passes, OK""") {
    val pass1 = mock[Pass]
    val pass2 = mock[Pass]
    expecting {
      pass1.name.andReturn("pass1").anyTimes()
      pass1.execute().andReturn(true)
      pass1.next().andReturn(Some(pass2))
      pass2.name.andReturn("pass2").anyTimes()
      pass2.execute().andReturn(true)
      pass2.next().andReturn(None)
    }
    // run the chain
    whenExecuting(pass1, pass2) {
      val options = new WriteablePassOptions()
      val executor = new PassChainExecutor(options, pass1)
      val result = executor.run()
      assert(result.isDefined)
      assert(result.contains(pass2))
    }
  }

  test("""2 passes, first fails""") {
    val pass1 = mock[Pass]
    val pass2 = mock[Pass]
    expecting {
      pass1.name.andReturn("pass1").anyTimes()
      pass1.execute().andReturn(false)
    }
    // run the chain
    whenExecuting(pass1, pass2) {
      val options = new WriteablePassOptions()
      val executor = new PassChainExecutor(options, pass1)
      val result = executor.run()
      assert(result.isEmpty)
    }
  }
}
