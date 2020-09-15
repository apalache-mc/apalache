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
    val intToInt = FunT1(IntT1(), IntT1())
    assert(unifier.unify(Substitution.empty, intToInt, intToInt).contains((Substitution.empty, intToInt)))
    val intAndBoolToInt = OperT1(Seq(IntT1(), BoolT1()), IntT1())
    assert(unifier.unify(Substitution.empty, intAndBoolToInt, intAndBoolToInt)
      .contains((Substitution.empty, intAndBoolToInt)))
    val tup1 = TupT1(IntT1(), BoolT1())
    assert(unifier.unify(Substitution.empty, tup1, tup1).contains((Substitution.empty, tup1)))
    val sparse1 = SparseTupT1(2 -> IntT1(), 4 -> BoolT1())
    val sparse2 = SparseTupT1(3 -> StrT1())
    val sparse3 = SparseTupT1(2 -> IntT1(), 3 -> StrT1(), 4 -> BoolT1())

    assert(unifier.unify(Substitution.empty, sparse1, sparse2).contains((Substitution.empty, sparse3)))
    val rec1 = RecT1("foo" -> BoolT1(), "bar" -> IntT1())
    val rec2 = RecT1("baz" -> StrT1())
    val rec3 = RecT1("foo" -> BoolT1(), "bar" -> IntT1(), "baz" -> StrT1())
    assert(unifier.unify(Substitution.empty, rec1, rec2).contains((Substitution.empty, rec3)))
  }

  test("non-unifying monotypes") {
    assert(unifier.unify(Substitution.empty, ConstT1("F"), BoolT1()).isEmpty)
    assert(unifier.unify(Substitution.empty, ConstT1("F"), ConstT1("G")).isEmpty)
    assert(unifier.unify(Substitution.empty, IntT1(), BoolT1()).isEmpty)
    assert(unifier.unify(Substitution.empty, BoolT1(), StrT1()).isEmpty)
    assert(unifier.unify(Substitution.empty, StrT1(), IntT1()).isEmpty)
    assert(unifier.unify(Substitution.empty, RealT1(), IntT1()).isEmpty)

    val intToInt = FunT1(IntT1(), IntT1())
    val boolToInt = FunT1(BoolT1(), IntT1())
    assert(unifier.unify(Substitution.empty, intToInt, boolToInt).isEmpty)
    val intAndBoolToInt = OperT1(Seq(IntT1(), BoolT1()), IntT1())
    val boolAndIntToInt = OperT1(Seq(BoolT1(), IntT1()), IntT1())
    assert(unifier.unify(Substitution.empty, intAndBoolToInt, boolAndIntToInt).isEmpty)
    val tup1 = TupT1(IntT1(), BoolT1())
    val tup2 = TupT1(IntT1(), StrT1())
    assert(unifier.unify(Substitution.empty, tup1, tup2).isEmpty)
    val sparse1 = SparseTupT1(2 -> IntT1(), 4 -> BoolT1())
    val sparse2 = SparseTupT1(2 -> IntT1(), 4 -> IntT1())
    assert(unifier.unify(Substitution.empty, sparse1, sparse2).isEmpty)
    val rec1 = RecT1("foo" -> BoolT1(), "bar" -> IntT1())
    val rec2 = RecT1("foo" -> BoolT1(), "bar" -> BoolT1())
    assert(unifier.unify(Substitution.empty, rec1, rec2).isEmpty)
  }

  test("unifying polytypes") {
    assert(unifier.unify(Substitution.empty, VarT1(0), IntT1())
      .contains((Substitution(0 -> IntT1()), IntT1())))
    assert(unifier.unify(Substitution.empty, FunT1(VarT1(0), IntT1()), FunT1(BoolT1(), VarT1(1)))
      .contains((Substitution(0 -> BoolT1(), 1 -> IntT1()), FunT1(BoolT1(), IntT1()))))

    val rec1 = RecT1("foo" -> BoolT1())
    val rec2 = RecT1("bar" -> IntT1())
    val rec3 = RecT1("foo" -> BoolT1(), "bar" -> IntT1())
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