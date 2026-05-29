package at.forsyte.apalache.io

import at.forsyte.apalache.infra.passes.options.{Config, SMTSolver}
import org.scalatest.funsuite.AnyFunSuite

class TestConfigManager extends AnyFunSuite {
  test("loads cvc5 as an SMT solver backend") {
    val config = ConfigManager("checker { smt-solver = cvc5 }").get

    assert(config.checker.smtSolver.contains(SMTSolver.CVC5))
  }

  test("serializes cvc5 as an SMT solver backend") {
    val config = Config.ApalacheConfig(checker = Config.Checker(smtSolver = Some(SMTSolver.CVC5)))

    assert(ConfigManager.serialize(config).contains("\"smt-solver\":\"cvc5\""))
  }
}
