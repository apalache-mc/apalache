package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.TlaOper
import org.junit.runner.RunWith
import org.scalacheck.Prop
import org.scalacheck.Prop.{AnyOperators, all, forAll, passed}
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers

/**
 * Tests of TlaDeclLevelFinder.
 */
@RunWith(classOf[JUnitRunner])
class TestTlaDeclLevelFinder extends FunSuite with Checkers {

  test("non-action operators + constants = constant level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered constants
    val operators = gens.simpleOperators ++ gens.setOperators ++ gens.logicOperators ++ gens.arithOperators
    val genDecl = gens.genTlaDeclButNotVar(gens.genTlaEx(operators))(_)
    val prop = forAll(gens.genTlaModuleWith(genDecl)) { module =>
      val finder = new TlaDeclLevelFinder(module)

      all(module.operDeclarations map {
        finder(_) =? TlaLevelConst
      }: _*) &&
      all(module.constDeclarations map {
        finder(_) =? TlaLevelConst
      }: _*)
    }
    check(prop, minSuccessful(500), sizeRange(4))
  }

  test("non-action operators + variables = state level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered constants
    val operators = gens.simpleOperators ++ gens.setOperators ++ gens.logicOperators ++ gens.arithOperators

    val prop = forAll(gens.genTlaModule(gens.genTlaEx(operators))) { module =>
      val finder = new TlaDeclLevelFinder(module)
      val vars = module.varDeclarations.map(_.name).toSet

      def expectedLevel(decl: TlaOperDecl): Prop = {
        val level = finder(decl)
        // it's hard to figure whether a declaration should be constant-level or state-level,
        // because operators may call one another
        s"operator ${decl.name}" |:
          (level =? TlaLevelState || level =? TlaLevelConst)
      }

      all(module.operDeclarations map expectedLevel: _*) &&
      all(module.constDeclarations map {
        finder(_) =? TlaLevelConst
      }: _*) &&
      all(module.varDeclarations map {
        finder(_) =? TlaLevelState
      }: _*)
    }
    check(prop, minSuccessful(1000), sizeRange(6))
  }

  test("action operators + variables = action level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered constants
    val operators = gens.actionOperators
    val prop = forAll(gens.genTlaModule(gens.genTlaEx(operators))) { module =>
      val finder = new TlaDeclLevelFinder(module)

      def expectedLevel(decl: TlaOperDecl): Prop = {
        val level = finder(decl)
        // it's hard to figure the exact level of a declaration,
        // because operators may call one another
        s"operator ${decl.name}" |:
          (level =? TlaLevelState || level =? TlaLevelConst || level =? TlaLevelAction)
      }

      all(module.operDeclarations map expectedLevel: _*) &&
      all(module.constDeclarations map {
        finder(_) =? TlaLevelConst
      }: _*) &&
      all(module.varDeclarations map {
        finder(_) =? TlaLevelState
      }: _*)
    }

    check(prop, minSuccessful(1000), sizeRange(6))
  }

  test("temporal operators + variables = temporal level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
      override val maxDeclsPerModule: Int = 4
    }
    // all names are considered constants
    val operators = gens.temporalOperators
    val genEx = gens.genTlaEx(operators)(_)
    val prop = forAll(gens.genTlaModuleWith(gens.genTlaOperDecl(genEx))) { module =>
      val finder = new TlaDeclLevelFinder(module)

      def expectedLevel(decl: TlaOperDecl): Prop = {
        val level = finder(decl)
        decl.body match {
          case OperEx(TlaOper.apply, _*) =>
            // this operator immediately applies another operator that may have a constant level
            passed

          case OperEx(_, _*) =>
            s"operator ${decl.name}" |:
              level =? TlaLevelTemporal

          case _ =>
            passed
        }
      }

      all(module.operDeclarations map expectedLevel: _*)
    }

    check(prop, minSuccessful(2000), sizeRange(5))
  }
}
