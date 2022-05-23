package at.forsyte.apalache.tla.lir

import org.junit.runner.RunWith
import org.scalacheck.Prop
import org.scalacheck.Prop.{all, forAll, passed, AnyOperators}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers
import _root_.at.forsyte.apalache.tla.lir.oper.TlaOper
import scala.collection.immutable.Set
import scala.collection.immutable.Seq

/**
 * Tests of TlaLevelFinder.
 */
@RunWith(classOf[JUnitRunner])
class TestLevelFinder extends AnyFunSuite with Checkers {

  test("expr: non-action operators + constants = constant level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered constants
    val module = TlaModule("test", Seq.empty[TlaDecl])
    val finder = new TlaLevelFinder(module)
    val operators =
      gens.simpleOperators ++ gens.setOperators ++ gens.functionOperators ++ gens.logicOperators ++ gens.arithOperators
    val prop = forAll(gens.genTlaEx(operators)(gens.emptyContext)) { ex =>
      finder.getLevelOfExpression(Set.empty[String], ex) ?= TlaLevelConst
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("expr: non-action operators + variables = state level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered variabels (TlaLevelState)
    val operators =
      gens.simpleOperators ++ gens.setOperators ++ gens.functionOperators ++ gens.logicOperators ++ gens.arithOperators
    val prop = forAll(gens.genTlaEx(operators)(gens.emptyContext)) { ex =>
      val module = TlaModule("test", Seq.empty[TlaDecl])
      val finder = new TlaLevelFinder(module)
      finder.levelCacheGetFun = _ => Some(TlaLevelState)
      val level = finder.getLevelOfExpression(Set.empty[String], ex)
      if (containsName(ex)) {
        level ?= TlaLevelState
      } else {
        level ?= TlaLevelConst
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("expr: action operators + variables = action level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered variables
    val operators = gens.actionOperators
    val prop = forAll(gens.genTlaEx(operators)(gens.emptyContext)) { ex =>
      val module = TlaModule("test", Seq.empty[TlaDecl])
      val finder = new TlaLevelFinder(module)
      finder.levelCacheGetFun = _ => Some(TlaLevelState)
      val level = finder.getLevelOfExpression(Set.empty[String], ex)
      ex match {
        case OperEx(_, _*) =>
          level ?= TlaLevelAction

        case _ =>
          passed
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("expr: temporal operators + variables = temporal level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered variabels
    val operators = gens.temporalOperators
    val prop = forAll(gens.genTlaEx(operators)(gens.emptyContext)) { ex =>
      val module = TlaModule("test", Seq.empty[TlaDecl])
      val finder = new TlaLevelFinder(module)
      finder.levelCacheGetFun = _ => Some(TlaLevelState)
      val level = finder.getLevelOfExpression(Set.empty[String], ex)
      ex match {
        case OperEx(_, _*) =>
          level ?= TlaLevelTemporal

        case _ =>
          passed
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  private def containsName: TlaEx => Boolean = {
    case NameEx(_) =>
      true

    case OperEx(_, args @ _*) =>
      args.map(containsName).foldLeft(false)(_ || _)

    case LetInEx(body, defs @ _*) =>
      defs.map(d => containsName(d.body)).foldLeft(containsName(body))(_ || _)

    case _ => false
  }

  test("decl: non-action operators + constants = constant level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    val operators =
      gens.simpleOperators ++ gens.setOperators ++ gens.functionOperators ++ gens.logicOperators ++ gens.arithOperators
    val genDecl = gens.genTlaDeclButNotVar(gens.genTlaEx(operators))(_)
    val prop = forAll(gens.genTlaModuleWith(genDecl)) { module =>
      val finder = new TlaLevelFinder(module)

      all(module.operDeclarations.map {
        finder.getLevelOfDecl(_) ?= TlaLevelConst
      }: _*) &&
      all(module.constDeclarations.map {
        finder.getLevelOfDecl(_) ?= TlaLevelConst
      }: _*)
    }
    check(prop, minSuccessful(500), sizeRange(4))
  }

  test("decl: non-action operators + variables = state level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    val operators =
      gens.simpleOperators ++ gens.setOperators ++ gens.functionOperators ++ gens.logicOperators ++ gens.arithOperators

    val prop = forAll(gens.genTlaModule(gens.genTlaEx(operators))) { module =>
      val finder = new TlaLevelFinder(module)
      // names are considered variables
      finder.levelCacheGetFun = _ => Some(TlaLevelState)

      def expectedLevel(decl: TlaOperDecl): Prop = {
        val level = finder.getLevelOfDecl(decl)
        // it's hard to figure whether a declaration should be constant-level or state-level,
        // because operators may call one another
        s"operator ${decl.name}" |:
          ((level ?= TlaLevelState) || (level ?= TlaLevelConst))
      }

      all(module.operDeclarations.map(expectedLevel): _*) &&
      all(module.constDeclarations.map {
        finder.getLevelOfDeclWithoutCacheCheck(_) ?= TlaLevelConst
      }: _*) &&
      all(module.varDeclarations.map {
        finder.getLevelOfDeclWithoutCacheCheck(_) ?= TlaLevelState
      }: _*)
    }
    check(prop, minSuccessful(1000), sizeRange(6))
  }

  test("decl: action operators + variables = action level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered variables
    val operators = gens.actionOperators
    val prop = forAll(gens.genTlaModule(gens.genTlaEx(operators))) { module =>
      val finder = new TlaLevelFinder(module)
      // names are considered variables
      finder.levelCacheGetFun = _ => Some(TlaLevelState)

      def expectedLevel(decl: TlaOperDecl): Prop = {
        val level = finder.getLevelOfDeclWithoutCacheCheck(decl)
        // it's hard to figure the exact level of a declaration,
        // because operators may call one another
        s"operator ${decl.name}" |:
          ((level ?= TlaLevelState) || (level ?= TlaLevelConst) || (level ?= TlaLevelAction))
      }

      all(module.operDeclarations.map(expectedLevel): _*) &&
      all(module.constDeclarations.map {
        finder.getLevelOfDeclWithoutCacheCheck(_) ?= TlaLevelConst
      }: _*) &&
      all(module.varDeclarations.map {
        finder.getLevelOfDeclWithoutCacheCheck(_) ?= TlaLevelState
      }: _*)
    }

    check(prop, minSuccessful(1000), sizeRange(6))
  }

  test("decl: temporal operators + variables = temporal level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
      override val maxDeclsPerModule: Int = 4
    }
    val operators = gens.temporalOperators
    val genEx = gens.genTlaEx(operators)(_)
    val prop = forAll(gens.genTlaModuleWith(gens.genTlaOperDecl(genEx))) { module =>
      val finder = new TlaLevelFinder(module)
      // names are considered variables
      finder.levelCacheGetFun = _ => Some(TlaLevelState)

      def expectedLevel(decl: TlaOperDecl): Prop = {
        val level = finder.getLevelOfDeclWithoutCacheCheck(decl)
        decl.body match {
          case OperEx(TlaOper.apply, _*) =>
            // this operator immediately applies another operator that may have a constant level
            passed

          case OperEx(_, _*) =>
            s"operator ${decl.name}" |:
              (level ?= TlaLevelTemporal)

          case _ =>
            passed
        }
      }

      all(module.operDeclarations.map(expectedLevel): _*)
    }

    check(prop, minSuccessful(2000), sizeRange(5))
  }
}
