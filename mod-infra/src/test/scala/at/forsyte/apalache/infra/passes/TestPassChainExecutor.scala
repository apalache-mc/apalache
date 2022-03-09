package at.forsyte.apalache.infra.passes

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}

@RunWith(classOf[JUnitRunner])
class TestPassChainExecutor extends AnyFunSuite {
  // Helper class to enable instantiation of different passes to be tested
  class ParametrizedPass(result: Boolean, deps: Set[ModuleProperty.Value], transfs: Set[ModuleProperty.Value])
      extends Pass {
    override def name = "TestPass"
    override def execute(tlaModule: TlaModule): Option[TlaModule] = {
      if (result) {
        Some(new TlaModule("TestModule", Seq()))
      } else {
        None
      }
    }
    override def dependencies = deps
    override def transformations = transfs
  }

  private val options = new WriteablePassOptions()

  test("""Executes a correctly ordered chain""") {
    val pass1 = new ParametrizedPass(true, Set(), Set(ModuleProperty.Inlined))
    val pass2 = new ParametrizedPass(true, Set(ModuleProperty.Inlined), Set())

    val executor = new PassChainExecutor(options, Seq(pass1, pass2))
    val result = executor.run()
    assert(result.isDefined)
  }

  test("""Throws error on a bad ordered chain""") {
    // Inlined is a unmet dependency
    val pass1 = new ParametrizedPass(true, Set(), Set())
    val pass2 = new ParametrizedPass(true, Set(ModuleProperty.Inlined), Set())

    val executor = new PassChainExecutor(options, Seq(pass1, pass2))
    val thrown = intercept[Exception] {
      executor.run()
    }

    assert(thrown.getMessage === "TestPass cannot run for a module without the properties: Inlined")
  }

  test("""Returns empty result when an execution is faulty""") {
    // execute() will return None for pass2
    val pass1 = new ParametrizedPass(true, Set(), Set())
    val pass2 = new ParametrizedPass(false, Set(), Set())

    val executor = new PassChainExecutor(options, Seq(pass1, pass2))

    val result = executor.run()
    assert(result.isEmpty)
  }
}
