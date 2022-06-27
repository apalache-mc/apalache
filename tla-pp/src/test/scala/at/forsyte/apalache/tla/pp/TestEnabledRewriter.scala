package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.IrGenerators
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestEnabledRewriter extends AnyFunSuite with Checkers {
  val gens = new IrGenerators {
    override val maxArgs: Int = 3
    override val allowUntypedExpressions: Boolean = false
  }

  // test with 3 different variables
  val context = Map[String, gens.UserOperSig]()

  val operators =
    gens.simpleOperators ++ gens.setOperators ++ gens.functionOperators ++ gens.logicOperators ++ gens.arithOperators
  val exGen = gens.genTlaEx(operators) _

  // test("test: each variable has a corresponding loop variable") {
  //   val prop = forAll(moduleGen) { module =>
  //     val output = loopEncoder.addLoopLogic(module, init, next)

  //     s"Transformed module: ${output.module.toString()}" |: Prop(module.varDeclarations.forall(varDecl => {
  //       val expectedLoopVarDecl = loopEncoder.createVarCopyVariableInLoop(varDecl)

  //       // check whether any variable declaration is the one declaring the loop variable
  //       output.module.varDeclarations.exists(newVarDecl => newVarDecl.name == expectedLoopVarDecl.name)
  //     }))
  //   }
  //   check(prop, minSuccessful(500), sizeRange(8))
  // }
}
