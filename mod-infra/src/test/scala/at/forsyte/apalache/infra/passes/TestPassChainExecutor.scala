package at.forsyte.apalache.infra.passes

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.easymock.EasyMockSugar
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.{TlaModule, ModuleProperty}

@RunWith(classOf[JUnitRunner])
class TestPassChainExecutor extends FunSuite {
  // Helper class to enable instantiation of different passes to be tested
  class ParametrizedPass(val nextPass: Pass with TlaModuleMixin, result: Boolean, deps: Set[ModuleProperty.Value],
      transfs: Set[ModuleProperty.Value])
      extends Pass with TlaModuleMixin {
    override def name = "TestPass"
    override def execute() = {
      nextPass.updateModule(this, new TlaModule("TestModule", Seq()))
      result
    }
    override def dependencies = deps
    override def transformations = transfs
  }

  private val terminalPass = new TerminalPassWithTlaModule
  private val options = new WriteablePassOptions()

  test("""Executes a correctly ordered chain""") {
    val pass2 = new ParametrizedPass(terminalPass, true, Set(ModuleProperty.Inlined), Set())
    val pass1 = new ParametrizedPass(pass2, true, Set(), Set(ModuleProperty.Inlined))

    val executor = new PassChainExecutor(options, pass1)
    val result = executor.run()
    assert(result.equals(Some(terminalPass)))
  }

  test("""Throws error on a bad ordered chain""") {
    // Inlined is a unmet dependency
    val pass2 = new ParametrizedPass(terminalPass, true, Set(ModuleProperty.Inlined), Set())
    val pass1 = new ParametrizedPass(pass2, true, Set(), Set())

    val executor = new PassChainExecutor(options, pass1)
    val thrown = intercept[Exception] {
      executor.run()
    }

    assert(thrown.getMessage === "TestPass cannot run for a module without the properties: Inlined")
  }

  test("""Returns empty result when an execution is faulty""") {
    // execute() will return false for pass2
    val pass2 = new ParametrizedPass(terminalPass, false, Set(), Set())
    val pass1 = new ParametrizedPass(pass2, true, Set(), Set())

    val executor = new PassChainExecutor(options, pass1)

    val result = executor.run()
    assert(result.isEmpty)
  }
}
