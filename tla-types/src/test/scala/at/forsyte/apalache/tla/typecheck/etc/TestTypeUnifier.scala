package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.typecheck.parser.DefaultType1Parser
import at.forsyte.apalache.tla.typecheck._
import org.junit.runner.RunWith
import org.scalatest.easymock.EasyMockSugar
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestTypeUnifier  extends FunSuite with EasyMockSugar with BeforeAndAfterEach with STCBuilder {
  private val parser: Type1Parser = DefaultType1Parser
  private var unifier: TypeUnifier = _

  override protected def beforeEach(): Unit = {
    unifier = new TypeUnifier()
  }

  test("unifying monotypes") {
    assert(unifier.unify(Substitution.empty, ConstT1("F"), ConstT1("F")).contains((Substitution.empty, ConstT1("F"))))
    assert(unifier.unify(Substitution.empty, IntT1(), IntT1()).contains((Substitution.empty, IntT1())))
    assert(unifier.unify(Substitution.empty, BoolT1(), BoolT1()).contains((Substitution.empty, BoolT1())))
    assert(unifier.unify(Substitution.empty, StrT1(), StrT1()).contains((Substitution.empty, StrT1())))
    assert(unifier.unify(Substitution.empty, RealT1(), RealT1()).contains((Substitution.empty, RealT1())))
    val intToInt = parser("Int -> Int")
    assert(unifier.unify(Substitution.empty, intToInt, intToInt).contains((Substitution.empty, intToInt)))
    val intAndBoolToInt = parser("(Int, Bool) => Int")
    assert(unifier.unify(Substitution.empty, intAndBoolToInt, intAndBoolToInt)
      .contains((Substitution.empty, intAndBoolToInt)))
    val tup1 =  parser("<<Int, Bool>>")
    assert(unifier.unify(Substitution.empty, tup1, tup1).contains((Substitution.empty, tup1)))
    val sparse1 = parser("{2: Int, 4: Bool}")
    val sparse2 = parser("{3: Str}")
    val sparse3 = parser("{2: Int, 3: Str, 4: Bool}")

    assert(unifier.unify(Substitution.empty, sparse1, sparse2).contains((Substitution.empty, sparse3)))
    val rec1 = parser("[foo: Bool, bar: Int]")
    val rec2 = parser("[baz: Str]")
    val rec3 = parser("[foo: Bool, bar: Int, baz: Str]")
    assert(unifier.unify(Substitution.empty, rec1, rec2).contains((Substitution.empty, rec3)))
  }

  test("non-unifying monotypes") {
    assert(unifier.unify(Substitution.empty, ConstT1("F"), BoolT1()).isEmpty)
    assert(unifier.unify(Substitution.empty, ConstT1("F"), ConstT1("G")).isEmpty)
    assert(unifier.unify(Substitution.empty, IntT1(), BoolT1()).isEmpty)
    assert(unifier.unify(Substitution.empty, BoolT1(), StrT1()).isEmpty)
    assert(unifier.unify(Substitution.empty, StrT1(), IntT1()).isEmpty)
    assert(unifier.unify(Substitution.empty, RealT1(), IntT1()).isEmpty)

    val intToInt = parser("Int -> Int")
    val boolToInt = parser("Bool -> Int")
    assert(unifier.unify(Substitution.empty, intToInt, boolToInt).isEmpty)
    val intAndBoolToInt = parser("(Int, Bool) => Int")
    val boolAndIntToInt = parser("(Bool, Int) => Int")
    assert(unifier.unify(Substitution.empty, intAndBoolToInt, boolAndIntToInt).isEmpty)
    val tup1 =  parser("<<Int, Bool>>")
    val tup2 =  parser("<<Int, Str>>")
    assert(unifier.unify(Substitution.empty, tup1, tup2).isEmpty)
    val sparse1 = parser("{2: Int, 4: Bool}")
    val sparse2 = parser("{2: Int, 4: Int}")
    assert(unifier.unify(Substitution.empty, sparse1, sparse2).isEmpty)
    val rec1 = parser("[foo: Bool, bar: Int]")
    val rec2 = parser("[foo: Bool, bar: Bool]")
    assert(unifier.unify(Substitution.empty, rec1, rec2).isEmpty)
  }

  test("unifying polytypes") {
    assert(unifier.unify(Substitution.empty, VarT1(0), IntT1())
      .contains((Substitution(0 -> IntT1()), IntT1())))
    assert(unifier.unify(Substitution.empty, FunT1(VarT1(0), IntT1()), FunT1(BoolT1(), VarT1(1)))
      .contains((Substitution(0 -> BoolT1(), 1 -> IntT1()), FunT1(BoolT1(), IntT1()))))

    val rec1 = parser("[foo: Bool]")
    val rec2 = parser("[bar: Int]")
    val rec3 = parser("[foo: Bool, bar: Int]")
    assert(unifier.unify(Substitution(0 -> rec1), VarT1(0), rec2)
      .contains((Substitution(0 -> rec3), rec3)))
  }

  test("unifying tricky polytypes") {
    assert(unifier.unify(Substitution.empty, VarT1(0), VarT1(0))
        .contains((Substitution.empty, VarT1(0))))
    assert(unifier.unify(Substitution(0 -> IntT1()), VarT1(0), VarT1(0))
      .contains((Substitution(0 -> IntT1()), IntT1())))
    assert(unifier.unify(Substitution.empty, VarT1(0), VarT1(1))
      .contains((Substitution(1 -> VarT1(0)), VarT1(0))))
    assert(unifier.unify(Substitution(1 -> IntT1()), VarT1(0), VarT1(1))
      .contains((Substitution(0 -> IntT1(), 1 -> IntT1()), IntT1())))
  }
}