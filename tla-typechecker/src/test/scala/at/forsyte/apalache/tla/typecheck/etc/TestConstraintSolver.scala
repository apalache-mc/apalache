package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.{OperT1, VarT1}
import at.forsyte.apalache.tla.types.TypeVarPool
import at.forsyte.apalache.tla.types.parser.{DefaultType1Parser, Type1Parser}
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.easymock.EasyMockSugar
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestConstraintSolver extends AnyFunSuite with EasyMockSugar with EtcBuilder {
  private val FIRST_VAR: Int = 100
  private val parser: Type1Parser = DefaultType1Parser

  test("unique solution") {
    val solver = new ConstraintSolver(new TypeVarPool(FIRST_VAR))
    // a disjunctive constraint that comes from a tuple constructor
    // either a == (b, c) => <<b, c>>
    val option1 = EqClause(VarT1("a"), OperT1(Seq(VarT1("b"), VarT1("c")), parser("<<b, c>>")))
    // or a == (d, d) => Seq(d)
    val option2 = EqClause(VarT1("a"), OperT1(Seq(VarT1("d"), VarT1("d")), parser("Seq(d)")))
    solver.addConstraint(OrClause(option1, option2))
    // an equation that comes from the operator application
    // a1 == (Int, Str) => e
    solver.addConstraint(EqClause(VarT1("a"), parser("(Int, Str) => e")))

    // there is a solution
    val solution = solver.solve()
    assert(solution.nonEmpty)
    assert(solution.map(_.subRec(VarT1("e"))).contains(parser("<<Int, Str>>")))
  }

  test("multiple solutions") {
    val solver = new ConstraintSolver(new TypeVarPool(FIRST_VAR))
    // a disjunctive constraint that comes from a tuple constructor
    // either a == (b, c) => <<b, c>>
    val option1 = EqClause(VarT1("a"), OperT1(Seq(VarT1("b"), VarT1("c")), parser("<<b, c>>")))
    // or a == (d, d) => Seq(d)
    val option2 = EqClause(VarT1("a"), OperT1(Seq(VarT1("d"), VarT1("d")), parser("Seq(d)")))
    solver.addConstraint(OrClause(option1, option2))
    // an equation that comes from the operator application
    // a1 == (Int, Str) => e
    solver.addConstraint(EqClause(VarT1("a"), parser("(Int, Int) => e")))

    // no solution
    val solution = solver.solve()
    assert(solution.isEmpty)
  }

  test("constraints in the reverse order") {
    val solver = new ConstraintSolver(new TypeVarPool(FIRST_VAR))
    // The following constraints come in the order that is reverse to the one that is required to solve the constraints.
    // These constraints are made up, they do not come from any real constraints that are produced by TLA+ operators.
    val eq1 = EqClause(VarT1("a"), parser("(b, c) => b"))
    val eq2 = EqClause(VarT1("a"), parser("(b, c) => c"))
    solver.addConstraint(OrClause(eq1, eq2))
    val eq3 = EqClause(VarT1("b"), parser("c"))
    val eq4 = EqClause(VarT1("b"), parser("Bool"))
    solver.addConstraint(OrClause(eq3, eq4))
    solver.addConstraint(EqClause(VarT1("c"), parser("Int")))
    solver.addConstraint(EqClause(VarT1("a"), parser("(Bool, d) => Int")))

    // there is a solution
    val solution = solver.solve()
    assert(solution.nonEmpty)
    assert(solution.map(_.subRec(VarT1("a"))).contains(parser("(Bool, Int) => Int")))
  }
}
