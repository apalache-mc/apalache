package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.IrGenerators
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.pp.temporal.LoopEncoder
import at.forsyte.apalache.tla.pp.temporal.utils.builder
import org.junit.runner.RunWith
import org.scalacheck.Prop
import org.scalacheck.Prop.forAll
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestLoopEncoder extends AnyFunSuite with Checkers {
  private val loopEncoder = new LoopEncoder(new IdleTracker())

  // loop encoder expects init and next declarations, so we generate empty ones to use when we don't care about them
  val init = builder.decl("init", builder.bool(true))
  val next = builder.decl("next", builder.bool(true))

  val gens = new IrGenerators {
    override val maxArgs: Int = 3
    override val allowUntypedExpressions: Boolean = false
  }

  val operators =
    gens.simpleOperators ++ gens.setOperators ++ gens.functionOperators ++ gens.logicOperators ++ gens.arithOperators
  val exGen = gens.genTlaEx(operators) _
  val moduleGen = gens.genTlaModule(exGen)

  test("test: each variable has a corresponding loop variable") {
    val prop = forAll(moduleGen) { module =>
      val output = loopEncoder.addLoopLogic(module, init, next)

      s"Transformed module: ${output.module.toString()}" |: Prop(module.varDeclarations.forall(varDecl => {
        val expectedLoopVarDecl = loopEncoder.createVarCopyVariableInLoop(varDecl)

        // check whether any variable declaration is the one declaring the loop variable
        output.module.varDeclarations.exists(newVarDecl => newVarDecl.name == expectedLoopVarDecl.name)
      }))
    }
    check(prop, minSuccessful(500), sizeRange(8))
  }

  test("test: there is a loopOK operator") {
    val prop = forAll(moduleGen) { module =>
      val output = loopEncoder.addLoopLogic(module, init, next)

      s"Transformed module: ${output.module.toString()}" |:
        // check whether any variable declaration is the one declaring the loop ok predicate
        Prop(output.module.operDeclarations.exists(operDecl => operDecl.name == LoopEncoder.LOOP_OK_NAME))
    }
    check(prop, minSuccessful(500), sizeRange(8))
  }

  test("test: there is an InLoop variable") {
    val prop = forAll(moduleGen) { module =>
      val output = loopEncoder.addLoopLogic(module, init, next)

      s"Transformed module: ${output.module.toString()}" |:
        // check whether any variable declaration is the one declaring the InLoop variable
        Prop(output.module.varDeclarations.exists(decl => decl.name == LoopEncoder.IN_LOOP_NAME))
    }
    check(prop, minSuccessful(500), sizeRange(8))
  }

  test("test: the InLoop variable does not have a loop copy") {
    // approximate this by ensuring that the name of any variable
    // which contains the name of the in loop variable
    // matches exactly that name
    val prop = forAll(moduleGen) { module =>
      val output = loopEncoder.addLoopLogic(module, init, next)

      s"Transformed module: ${output.module.toString()}" |: Prop(
          !output.module.varDeclarations.exists(decl =>
            decl.name.contains(LoopEncoder.IN_LOOP_NAME) && decl.name != LoopEncoder.IN_LOOP_NAME)
      )
    }
    check(prop, minSuccessful(500), sizeRange(8))
  }
}
