package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.BoolT1
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.TlaLevelFinder
import at.forsyte.apalache.tla.lir.TlaLevelTemporal
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.TlaOperDecl
import at.forsyte.apalache.tla.lir.Typed
import at.forsyte.apalache.tla.lir.ValEx
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.oper.TlaTempOper
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.pp.temporal.LoopEncoder
import at.forsyte.apalache.tla.pp.temporal.utils.builder
import at.forsyte.apalache.tla.pp.temporal.TableauEncoder
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalacheck.Gen.oneOf
import org.scalacheck.Prop
import org.scalacheck.Prop.AnyOperators
import org.scalacheck.Prop.forAll
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestTableauEncoder extends AnyFunSuite with Checkers {
  private val loopEncoder = new LoopEncoder(new IdleTracker())

  // loop encoder expects init and next declarations, so we generate empty ones to use when we don't care about them
  val init = builder.decl("init", builder.bool(true))
  val next = builder.decl("next", builder.bool(true))
  val module = new TlaModule("module", List(init, next))
  val modWithPreds = loopEncoder.addLoopLogic(module, init, next)

  val levelFinder = new TlaLevelFinder(modWithPreds.module)

  private val tableauEncoder =
    new TableauEncoder(
        modWithPreds.module,
        new UniqueNameGenerator(),
        loopEncoder,
        new IdleTracker(),
    )

  // ad hoc builder for well-typed temporal expressions (everything is typed boolean)
  def formulaGen: Gen[TlaEx] = Gen.sized { size =>
    for {
      // size is the number of operators
      op <- oneOf(TlaBoolOper.and, TlaBoolOper.or, TlaTempOper.box, TlaTempOper.diamond)
      innerGen: Gen[TlaEx] =
        if (size > 1) {
          Gen.resize(size - 1, formulaGen)
        } else {
          Gen.oneOf(
              ValEx(TlaBool(false))(Typed(BoolT1)),
              ValEx(TlaBool(true))(Typed(BoolT1)),
          )
        }
      args <- Gen.containerOfN[List, TlaEx](if (op == TlaBoolOper.and || op == TlaBoolOper.or) 2 else 1, innerGen)
    } yield op match {
      case TlaBoolOper.and => builder.and(args.map(ex => builder.unchecked(ex)): _*)
      case TlaBoolOper.or  => builder.or(args.map(ex => builder.unchecked(ex)): _*)
      case _: TlaTempOper  => OperEx(op, args: _*)(Typed(BoolT1))
    }
  }

  def computeNumberOfNodes(ex: TlaEx): Int = {
    levelFinder.getLevelOfExpression(Set.empty, ex) match {
      case TlaLevelTemporal =>
        ex match {
          case OperEx(_, args @ _*) => args.foldLeft(1)((acc, ex) => acc + computeNumberOfNodes(ex))
          case _                    => 0
        }
      case _ => 0
    }
  }

  def countOperatorApplications(opp: TlaOper, ex: TlaEx): Int = {
    ex match {
      case OperEx(oper, args @ _*) =>
        args.foldLeft(if (oper == opp) 1 else 0)((acc, ex) => acc + countOperatorApplications(opp, ex))
      case _ => 0
    }
  }

  test("test: there is a variable for each node of the syntax tree that is of temporal level") {
    val prop = forAll(formulaGen) { formula =>
      if (levelFinder.getLevelOfExpression(Set.empty, formula) != TlaLevelTemporal) {
        Prop.undecided
      } else {
        val output =
          tableauEncoder
            .temporalsToInvariants(modWithPreds, new TlaOperDecl("__formula", List.empty, formula)(Typed(BoolT1)))

        val nodesInFormulaSyntaxTree = computeNumberOfNodes(formula)

        // identify predicate variables by the variable names
        val predicateVariables = output.varDeclarations
          .filter(decl =>
            decl.name.startsWith(TableauEncoder.NAME_PREFIX)
              && !decl.name.contains(LoopEncoder.NAME_PREFIX)
              && !decl.name.contains(TableauEncoder.BOX_SUFFIX)
              && !decl.name.contains(TableauEncoder.DIAMOND_SUFFIX))
          .length

        nodesInFormulaSyntaxTree ?= predicateVariables
      }
    }
    check(prop, minSuccessful(500), sizeRange(4))
  }

  test("test: there is a loop variable for each node of the syntax tree that is of temporal level") {
    val prop = forAll(formulaGen) { formula =>
      if (levelFinder.getLevelOfExpression(Set.empty, formula) != TlaLevelTemporal) {
        Prop.undecided
      }
      val output =
        tableauEncoder
          .temporalsToInvariants(modWithPreds, new TlaOperDecl("__formula", List.empty, formula)(Typed(BoolT1)))

      val nodesInFormulaSyntaxTree = computeNumberOfNodes(formula)

      // identify predicate variables by the variable names
      val loopPredicateVariables = output.varDeclarations
        .filter(decl =>
          decl.name.startsWith(LoopEncoder.NAME_PREFIX + TableauEncoder.NAME_PREFIX)
            && !decl.name.endsWith(TableauEncoder.BOX_SUFFIX)
            && !decl.name.endsWith(TableauEncoder.DIAMOND_SUFFIX))
        .length

      nodesInFormulaSyntaxTree ?= loopPredicateVariables
    }
    check(prop, minSuccessful(500), sizeRange(4))
  }

  if (TableauEncoder.DIAMOND_SUFFIX != TableauEncoder.BOX_SUFFIX) {

    test("test: for each box operator, there are two extra variables") {
      val prop = forAll(formulaGen) { formula =>
        if (levelFinder.getLevelOfExpression(Set.empty, formula) != TlaLevelTemporal) {
          Prop.undecided
        }
        val output =
          tableauEncoder
            .temporalsToInvariants(modWithPreds, new TlaOperDecl("__formula", List.empty, formula)(Typed(BoolT1)))

        val boxApplications = countOperatorApplications(TlaTempOper.box, formula)

        // identify predicate variables by the variable names
        val boxVariables = output.varDeclarations
          .filter(decl => decl.name.endsWith(TableauEncoder.BOX_SUFFIX))
          .length

        boxApplications ?= boxVariables

        val prevBoxVariables = output.varDeclarations
          .filter(decl => decl.name.endsWith(TableauEncoder.BOX_SUFFIX + TableauEncoder.LOOKBACK_SUFFIX))
          .length

        boxApplications ?= prevBoxVariables
      }
      check(prop, minSuccessful(500), sizeRange(4))
    }

    test("test: for each diamond operator, there are two extra variables") {
      val prop = forAll(formulaGen) { formula =>
        if (levelFinder.getLevelOfExpression(Set.empty, formula) != TlaLevelTemporal) {
          Prop.undecided
        }
        val output =
          tableauEncoder
            .temporalsToInvariants(modWithPreds, new TlaOperDecl("__formula", List.empty, formula)(Typed(BoolT1)))

        val diamondApplications = countOperatorApplications(TlaTempOper.diamond, formula)

        // identify predicate variables by the variable names
        val diamondVariables = output.varDeclarations
          .filter(decl => decl.name.endsWith(TableauEncoder.DIAMOND_SUFFIX))
          .length

        diamondApplications ?= diamondVariables

        val prevDiamondVariables = output.varDeclarations
          .filter(decl => decl.name.endsWith(TableauEncoder.DIAMOND_SUFFIX + TableauEncoder.LOOKBACK_SUFFIX))
          .length

        diamondApplications ?= prevDiamondVariables
      }
      check(prop, minSuccessful(500), sizeRange(4))
    }
  } else { // TableauEncoder.DIAMOND_SUFFIX == TableauEncoder.BOX_SUFFIX)
    test("test: for each diamond and box operator, there are two extra variables") {
      val prop = forAll(formulaGen) { formula =>
        if (levelFinder.getLevelOfExpression(Set.empty, formula) != TlaLevelTemporal) {
          Prop.undecided
        }
        val output =
          tableauEncoder
            .temporalsToInvariants(modWithPreds, new TlaOperDecl("__formula", List.empty, formula)(Typed(BoolT1)))

        val temporalApplications =
          countOperatorApplications(TlaTempOper.diamond, formula) + countOperatorApplications(TlaTempOper.box, formula)

        // identify predicate variables by the variable names
        val temporalAuxVars = output.varDeclarations
          // since BOX_SUFFIX and DIAMOND_SUFFIX are the same, doesn't matter which we choose
          .filter(decl => decl.name.endsWith(TableauEncoder.DIAMOND_SUFFIX))
          .length

        temporalApplications ?= temporalAuxVars

        val prevTemporalAuxVars = output.varDeclarations
          .filter(decl => decl.name.endsWith(TableauEncoder.DIAMOND_SUFFIX + TableauEncoder.LOOKBACK_SUFFIX))
          .length

        temporalApplications ?= prevTemporalAuxVars
      }
      check(prop, minSuccessful(500), sizeRange(4))
    }
  }
}
