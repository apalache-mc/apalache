package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.infra.{ExceptionAdapter, ExitCodes}
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.infra.passes.options.OptionGroup.WithNone
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule}

/**
 * Helper class to enable instantiation of different passes to be tested.
 */
class ParametrizedPass(result: Boolean, deps: Set[ModuleProperty.Value], transfs: Set[ModuleProperty.Value])
    extends Pass {
  override def name = "TestPass"
  override def execute(tlaModule: TlaModule): PassResult = {
    if (result) {
      Right(TlaModule("TestModule", Seq()))
    } else {
      passFailure(None, ExitCodes.ERROR)
    }
  }
  override def dependencies: Set[ModuleProperty.Value] = deps
  override def transformations: Set[ModuleProperty.Value] = transfs
}

class Pass1 extends ParametrizedPass(true, Set(), Set(ModuleProperty.Inlined))
class Pass2 extends ParametrizedPass(true, Set(ModuleProperty.Inlined), Set())
class Pass3 extends ParametrizedPass(true, Set(), Set())
class Pass4 extends ParametrizedPass(false, Set(), Set())

class DummyExceptionAdapter extends ExceptionAdapter {}

/**
 * A dummy tool module that allows to test the pass chain executor.
 * @param passesToExecute
 *   the sequence of passes that this module will execute
 */
class DummyToolModule(passesToExecute: Class[_ <: Pass]*) extends ToolModule(WithNone()) {
  override def passes: Seq[Class[_ <: Pass]] = passesToExecute

  override def configure(): Unit = {
    // No configuration needed for this dummy module
    bind(classOf[ExceptionAdapter])
      .to(classOf[DummyExceptionAdapter])
  }
}

@RunWith(classOf[JUnitRunner])
class TestPassChainExecutor extends AnyFunSuite {
  test("""Executes a correctly ordered chain""") {
    val result = PassChainExecutor(new DummyToolModule(classOf[Pass1], classOf[Pass2])).run()
    assert(result.isRight)
  }

  test("""Throws error on a bad ordered chain""") {
    // Inlined is a unmet dependency
    val thrown = intercept[Exception] {
      PassChainExecutor(new DummyToolModule(classOf[Pass3], classOf[Pass2])).run()
    }

    assert(thrown.getMessage === "TestPass cannot run for a module without the properties: Inlined")
  }

  test("""Returns empty result when an execution is faulty""") {
    // execute() will return None for pass2
    val result = PassChainExecutor(new DummyToolModule(classOf[Pass3], classOf[Pass4])).run()
    assert(result.isLeft)
  }
}
