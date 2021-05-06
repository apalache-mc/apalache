package at.forsyte.apalache.tla.lir

import org.junit.runner.RunWith
import org.scalacheck.Prop.{AnyOperators, forAll, passed}
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers

/**
 * Tests of TlaLevelFinder.
 */
@RunWith(classOf[JUnitRunner])
class TestTlaExLevelFinder extends FunSuite with Checkers {

  test("non-action operators + constants = constant level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered constants
    val finder = new TlaExLevelFinder({ _ => TlaLevelConst })
    val operators = gens.simpleOperators ++ gens.setOperators ++ gens.logicOperators ++ gens.arithOperators
    val prop = forAll(gens.genTlaEx(operators)(gens.emptyContext)) { ex =>
      finder(ex) =? TlaLevelConst
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("non-action operators + variables = state level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered constants
    val operators = gens.simpleOperators ++ gens.setOperators ++ gens.logicOperators ++ gens.arithOperators
    val prop = forAll(gens.genTlaEx(operators)(gens.emptyContext)) { ex =>
      val finder = new TlaExLevelFinder(_ => TlaLevelState)
      val level = finder(ex)
      if (containsName(ex)) {
        level =? TlaLevelState
      } else {
        level =? TlaLevelConst
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("action operators + variables = action level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered constants
    val operators = gens.actionOperators
    val prop = forAll(gens.genTlaEx(operators)(gens.emptyContext)) { ex =>
      val finder = new TlaExLevelFinder(_ => TlaLevelState)
      val level = finder(ex)
      ex match {
        case OperEx(_, _*) =>
          level =? TlaLevelAction

        case _ =>
          passed
      }
    }
    check(prop, minSuccessful(2500), sizeRange(8))
  }

  test("temporal operators + variables = temporal level") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 3
    }
    // all names are considered constants
    val operators = gens.temporalOperators
    val prop = forAll(gens.genTlaEx(operators)(gens.emptyContext)) { ex =>
      val finder = new TlaExLevelFinder(_ => TlaLevelState)
      val level = finder(ex)
      ex match {
        case OperEx(_, _*) =>
          level =? TlaLevelTemporal

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
}
