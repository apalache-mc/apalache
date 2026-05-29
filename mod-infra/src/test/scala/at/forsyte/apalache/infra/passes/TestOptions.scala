package at.forsyte.apalache.infra.passes.options

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import scala.util.{Failure, Success}

@RunWith(classOf[JUnitRunner])
class TestOptions extends AnyFunSuite {
  test("Can construct SourceOption.FileSource for ITF files") {
    import SourceOption._
    assert(FileSource(new java.io.File("foo.itf.json")).map(_.format) == Success(Format.Itf))
  }

  test("Non-ITF JSON files are not recognized as ITF format") {
    import SourceOption._

    assert(FileSource(new java.io.File("foo.json")).map(_.format) == Success(Format.Json))
  }

  test("CVC5 currently supports only the OOPSLA19 SMT encoding") {
    Seq(SMTEncoding.OOPSLA19, SMTEncoding.Arrays, SMTEncoding.FunArrays).foreach { encoding =>
      val config = Config.Checker(
          smtSolver = Some(SMTSolver.Z3),
          smtEncoding = Some(encoding),
      )

      assert(OptionGroup.Checker(config).isSuccess)
    }

    val cvc5OopslaConfig = Config.Checker(
        smtSolver = Some(SMTSolver.CVC5),
        smtEncoding = Some(SMTEncoding.OOPSLA19),
    )
    assert(OptionGroup.Checker(cvc5OopslaConfig).isSuccess)

    val config = Config.Checker(
        smtSolver = Some(SMTSolver.CVC5),
        smtEncoding = Some(SMTEncoding.Arrays),
    )

    OptionGroup.Checker(config) match {
      case Failure(error) =>
        assert(error.getMessage.contains("checker.smt-solver=cvc5"))
        assert(error.getMessage.contains("checker.smt-encoding=oopsla19"))
        assert(error.getMessage.contains("arrays"))

      case Success(options) =>
        fail(s"Expected the CVC5 arrays configuration to be rejected, but got $options")
    }
  }
}
