package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.io.typecheck.parser.{DefaultType1Parser, Type1Parser}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.{TypeUnifier, TypeVarPool}
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.easymock.EasyMockSugar
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTypeUnifier extends AnyFunSuite with EasyMockSugar with BeforeAndAfterEach with EtcBuilder {
  private val FIRST_VAR: Int = 100
  private val parser: Type1Parser = DefaultType1Parser
  private var unifier: TypeUnifier = _

  override protected def beforeEach(): Unit = {
    unifier = new TypeUnifier(new TypeVarPool(FIRST_VAR))
  }

  test("unifying monotypes") {
    assert(unifier.unify(Substitution.empty, ConstT1("F"), ConstT1("F")).contains((Substitution.empty, ConstT1("F"))))
    assert(unifier.unify(Substitution.empty, IntT1, IntT1).contains((Substitution.empty, IntT1)))
    assert(unifier.unify(Substitution.empty, BoolT1, BoolT1).contains((Substitution.empty, BoolT1)))
    assert(unifier.unify(Substitution.empty, StrT1, StrT1).contains((Substitution.empty, StrT1)))
    assert(unifier.unify(Substitution.empty, RealT1, RealT1).contains((Substitution.empty, RealT1)))
    val intToInt = parser("Int -> Int")
    assert(unifier.unify(Substitution.empty, intToInt, intToInt).contains((Substitution.empty, intToInt)))
    val intAndBoolToInt = parser("(Int, Bool) => Int")
    assert(unifier
          .unify(Substitution.empty, intAndBoolToInt, intAndBoolToInt)
          .contains((Substitution.empty, intAndBoolToInt)))
    val tup1 = parser("<<Int, Bool>>")
    assert(unifier.unify(Substitution.empty, tup1, tup1).contains((Substitution.empty, tup1)))

    val sparse1 = parser("<| 2: Int, 4: Bool |>")
    val sparse2 = parser("<| 3: Str |>")
    val sparse3 = parser("<| 2: Int, 3: Str, 4: Bool |>")
    val sparse4 = parser("<| 1: Int |>")
    assert(unifier.unify(Substitution.empty, sparse1, sparse2).contains((Substitution.empty, sparse3)))
    assert(unifier.unify(Substitution.empty, tup1, sparse4).contains((Substitution.empty, tup1)))
    assert(unifier.unify(Substitution.empty, sparse4, tup1).contains((Substitution.empty, tup1)))

    val rec1 = parser("[foo: Bool, bar: Int]")
    val rec2 = parser("[baz: Str]")
    val rec3 = parser("[foo: Bool, bar: Int, baz: Str]")
    assert(unifier.unify(Substitution.empty, rec1, rec2).contains((Substitution.empty, rec3)))
  }

  test("non-unifying monotypes") {
    assert(unifier.unify(Substitution.empty, ConstT1("F"), BoolT1).isEmpty)
    assert(unifier.unify(Substitution.empty, ConstT1("F"), ConstT1("G")).isEmpty)
    assert(unifier.unify(Substitution.empty, IntT1, BoolT1).isEmpty)
    assert(unifier.unify(Substitution.empty, BoolT1, StrT1).isEmpty)
    assert(unifier.unify(Substitution.empty, StrT1, IntT1).isEmpty)
    assert(unifier.unify(Substitution.empty, RealT1, IntT1).isEmpty)

    val intToInt = parser("Int -> Int")
    val boolToInt = parser("Bool -> Int")
    assert(unifier.unify(Substitution.empty, intToInt, boolToInt).isEmpty)
    val intAndBoolToInt = parser("(Int, Bool) => Int")
    val boolAndIntToInt = parser("(Bool, Int) => Int")
    assert(unifier.unify(Substitution.empty, intAndBoolToInt, boolAndIntToInt).isEmpty)
    val tup1 = parser("<<Int, Bool>>")
    val tup2 = parser("<<Int, Str>>")
    val tup3 = parser("<<Str, Int>>")
    assert(unifier.unify(Substitution.empty, tup1, tup2).isEmpty)
    assert(unifier.unify(Substitution.empty, tup2, tup3).isEmpty)

    val sparse1 = parser("<| 2: Int, 4: Bool |>")
    val sparse2 = parser("<| 2: Int, 4: Int |>")
    assert(unifier.unify(Substitution.empty, sparse1, sparse2).isEmpty)
    // a sparse tuple is not allowed to extend the tuple domain
    assert(unifier.unify(Substitution.empty, tup3, sparse1).isEmpty)

    val rec1 = parser("[foo: Bool, bar: Int]")
    val rec2 = parser("[foo: Bool, bar: Bool]")
    assert(unifier.unify(Substitution.empty, rec1, rec2).isEmpty)
  }

  test("unifying polytypes") {
    assert(unifier
          .unify(Substitution.empty, VarT1(0), IntT1)
          .contains((Substitution(EqClass(0) -> IntT1), IntT1)))
    assert(unifier
          .unify(Substitution.empty, FunT1(VarT1(0), IntT1), FunT1(BoolT1, VarT1(1)))
          .contains((Substitution(EqClass(0) -> BoolT1, EqClass(1) -> IntT1), FunT1(BoolT1, IntT1))))
    assert(unifier
          .unify(Substitution.empty, VarT1(0), ConstT1("ID"))
          .contains((Substitution(EqClass(0) -> ConstT1("ID")), ConstT1("ID"))))
    assert(unifier
          .unify(Substitution.empty, ConstT1("ID"), VarT1(0))
          .contains((Substitution(EqClass(0) -> ConstT1("ID")), ConstT1("ID"))))

    val rec1 = parser("[foo: Bool]")
    val rec2 = parser("[bar: Int]")
    val rec3 = parser("[foo: Bool, bar: Int]")
    assert(unifier
          .unify(Substitution(EqClass(0) -> rec1), VarT1(0), rec2)
          .contains((Substitution(EqClass(0) -> rec3), rec3)))
  }

  test("unifying tricky polytypes") {
    assert(unifier
          .unify(Substitution.empty, VarT1(0), VarT1(0))
          .contains((Substitution(EqClass(0) -> VarT1(0)), VarT1(0))))
    assert(unifier
          .unify(Substitution(EqClass(0) -> IntT1), VarT1(0), VarT1(0))
          .contains((Substitution(EqClass(0) -> IntT1), IntT1)))
    assert(unifier
          .unify(Substitution.empty, VarT1(0), VarT1(1))
          .contains((Substitution(EqClass(Set(0, 1)) -> VarT1(0)), VarT1(0))))
    assert(unifier
          .unify(Substitution(EqClass(1) -> IntT1), VarT1(0), VarT1(1))
          .contains((Substitution(EqClass(Set(0, 1)) -> IntT1), IntT1)))
    // unify <<a, b>> and <<b, a>>
    assert(unifier
          .unify(Substitution.empty, parser("<<a, b>>"), parser("<<b, a>>"))
          .contains((Substitution(EqClass(Set(0, 1)) -> VarT1(0)), parser("<<a, a>>"))))
    // there is no problem with the cycle a -> b -> c -> a
    val expectedSub = Substitution(EqClass(Set(0, 1, 2)) -> VarT1(0))
    assert(unifier
          .unify(Substitution.empty, parser("<<a, b, c>>"), parser("<<b, c, a>>"))
          .contains((expectedSub, parser("<<a, a, a>>"))))
  }

  test("unifying Seq(a) and Seq(Int)") {
    assert(unifier
          .unify(Substitution.empty, SeqT1(VarT1(0)), SeqT1(IntT1))
          .contains((Substitution(EqClass(0) -> IntT1), SeqT1(IntT1))))
  }

  test("unifying a => Set(a) and Int => b") {
    assert(unifier
          .unify(Substitution.empty, OperT1(Seq(VarT1(0)), SetT1(VarT1(0))), OperT1(Seq(IntT1), VarT1(1)))
          .contains((Substitution(EqClass(0) -> IntT1, EqClass(1) -> SetT1(VarT1(0))),
                  OperT1(Seq(IntT1), SetT1(IntT1)))))
  }

  test("non-unifying polytypes") {
    // a and Set(a) must be non-unifiable
    assert(unifier.unify(Substitution.empty, parser("a"), parser("Set(a)")).isEmpty)
  }

  test("unifying with transitivity") {
    val expectedSubstitution = Substitution(EqClass(Set(1, 2)) -> parser("PERSON"))
    assert(unifier
          .unify(Substitution.empty, parser("Set(b) -> Set(b)"), parser("Set(c) -> Set(PERSON)"))
          .contains((expectedSubstitution, parser("Set(PERSON) -> Set(PERSON)"))))
  }

  // regression
  test("unifying variables via sets") {
    val sub = Substitution(EqClass(1003) -> SetT1(VarT1(0)), EqClass(1004) -> SetT1(VarT1(1005)))
    val expected =
      Substitution(EqClass(Set(1003, 1004)) -> SetT1(VarT1(0)), EqClass(Set(0, 1005)) -> VarT1(0))
    assert(unifier
          .unify(sub, VarT1(1004), VarT1(1003))
          .contains((expected, SetT1(VarT1(0)))))
  }

  // regression
  test("unifying variables via operators") {
    val sub = Substitution(
        EqClass(Set(1000, 1004)) -> VarT1(1000),
        EqClass(1005) -> OperT1(Seq(VarT1(1000)), VarT1(1001)),
        EqClass(1006) -> VarT1(1000),
    ) ////
    val expected = Substitution(
        EqClass(Set(1000, 1001, 1004, 1006)) -> VarT1(1000),
        EqClass(1005) -> OperT1(Seq(VarT1(1000)), VarT1(1000)),
    ) ////
    assert(unifier
          .unify(sub, VarT1(1005), OperT1(Seq(VarT1(1004)), VarT1(1006)))
          .contains((expected, OperT1(Seq(VarT1(1000)), VarT1(1000)))))
  }

  test("unifying an empty row with a non-empty") {
    val d = VarT1("d")
    val row1 = parser("(| |)")
    val row2 = parser("(| d |)")
    val expectedSub = Substitution(
        EqClass(Set(d.no)) -> RowT1()
    ) ///
    val result = unifier.unify(Substitution(), row1, row2)
    assert(result.contains((expectedSub, parser("(| |)"))))
  }

  test("unifying an empty row with a var") {
    val row1 = parser("(| |)")
    val row2 = parser("(| field1: Int |)")
    val result = unifier.unify(Substitution(), row1, row2)
    assert(result.isEmpty)
  }

  test("unifying a single var with a single field + var") {
    val c = VarT1("c")
    val d = VarT1("d")
    val row1 = parser("(| c |)")
    val row2 = parser("(| field1: Int | d |)")
    val expectedSub = Substitution(
        EqClass(Set(c.no)) -> parser("(| field1: Int | d |)"),
        EqClass(Set(d.no)) -> d,
    ) ///
    val result = unifier.unify(Substitution(), row1, row2)
    assert(result.contains((expectedSub, parser("(| field1: Int | d |)"))))
  }

  test("unifying two partial rows") {
    val c = VarT1("c")
    val d = VarT1("d")
    val fresh = VarT1(FIRST_VAR)
    val row1 = parser("(| field1: Int | field2: Str | c |)")
    val row2 = parser("(| field3: Bool | d |)")
    val expectedSub = Substitution(
        EqClass(Set(c.no)) -> RowT1(fresh, "field3" -> BoolT1),
        EqClass(Set(d.no)) -> RowT1(fresh, "field1" -> IntT1, "field2" -> StrT1),
        EqClass(Set(fresh.no)) -> fresh,
    ) ///
    val result = unifier.unify(Substitution(), row1, row2)
    assert(result.contains((expectedSub, parser("(| field1: Int | field2: Str | field3: Bool | %s |)".format(fresh)))))
  }

  test("unifying a partial row + a complete row") {
    val d = VarT1("d")
    val row1 = parser("(| field2: Str | d |)")
    val row2 = parser("(| field1: Int | field2: Str | field3: Bool |)")
    val expectedSub = Substitution(
        EqClass(Set(d.no)) -> parser("(| field1: Int | field3: Bool |)")
    ) ///
    val result = unifier.unify(Substitution(), row1, row2)
    assert(result.contains((expectedSub, parser("(| field1: Int | field2: Str | field3: Bool |)"))))
  }

  test("unifying a complete row + a partial row") {
    val d = VarT1("d")
    val row1 = parser("(| field1: Int | field2: Str |)")
    val row2 = parser("(| field2: Str | d |)")
    val expectedSub = Substitution(
        EqClass(Set(d.no)) -> parser("(| field1: Int |)")
    ) ///
    val result = unifier.unify(Substitution(), row1, row2)
    assert(result.contains((expectedSub, parser("(| field1: Int | field2: Str |)"))))
  }

  test("unifying two rows with variables") {
    val c = VarT1("c")
    val d = VarT1("d")
    val row1 = parser("(| c |)")
    val row2 = parser("(| d |)")
    val expectedSub = Substitution(
        EqClass(Set(c.no, d.no)) -> c
    ) ///
    val result = unifier.unify(Substitution(), row1, row2)
    assert(result.contains((expectedSub, parser("(| c |)"))))
  }

  test("unifying two rows with incompatible variables") {
    val c = VarT1("c")
    val d = VarT1("d")
    val row1 = parser("(| c |)")
    val row2 = parser("(| d |)")
    val inputSub = Substitution(
        EqClass(c.no) -> parser("(| field1: Int |)"),
        EqClass(d.no) -> parser("(| field1: Bool |)"),
    )
    val result = unifier.unify(inputSub, row1, row2)
    assert(result.isEmpty)
  }

  test("unifying two complete rows") {
    val row1 = parser("(| field1: Int | field2: Str |)")
    val row2 = parser("(| field3: Bool |)")
    val result = unifier.unify(Substitution(), row1, row2)
    assert(result.isEmpty)
  }

  test("unifying rows with an incompatible field") {
    val row1 = parser("(| field1: Int |)")
    val row2 = parser("(| field1: Str |)")
    val result = unifier.unify(Substitution(), row1, row2)
    assert(result.isEmpty)
  }

  test("unifying rows that have disjoint fields and a shared one") {
    val row1 = parser("(| shared: Bool | field1: Int |)")
    val row2 = parser("(| shared: Bool | field2: Str |)")
    val result = unifier.unify(Substitution(), row1, row2)
    assert(result.isEmpty)
  }

  test("unifying records with compatible fields") {
    val c = VarT1("c")
    val d = VarT1("d")
    val rec1 = parser("{ field1: Int, c }")
    val rec2 = parser("{ field2: Str, d }")
    val expectedSub = Substitution(
        EqClass(Set(c.no)) -> parser("(| field2: Str | a100 |)"),
        EqClass(Set(d.no)) -> parser("(| field1: Int | a100 |)"),
        EqClass(Set(FIRST_VAR)) -> VarT1(FIRST_VAR),
    ) ///
    val result = unifier.unify(Substitution(), rec1, rec2)
    assert(result.contains((expectedSub, parser("{ field1: Int, field2: Str, a100 }"))))
  }

  test("unifying a partial record with a complete record") {
    val c = VarT1("c")
    val d = VarT1("d")
    val rec1 = parser("{ field2: c, d }")
    val rec2 = parser("{ field2: Str, field3: Bool }")
    val expectedSub = Substitution(
        EqClass(Set(c.no)) -> parser("Str"),
        EqClass(Set(d.no)) -> parser("(| field3: Bool |)"),
    ) ///
    val result = unifier.unify(Substitution(), rec1, rec2)
    assert(result.contains((expectedSub, parser("{ field2: Str, field3: Bool }"))))
  }

  test("unifying an extra field with a complete record") {
    val rec1 = parser("{ field1: Int, c }")
    val rec2 = parser("{ field2: Str, field3: Bool }")
    val result = unifier.unify(Substitution(), rec1, rec2)
    assert(result.isEmpty)
  }

  test("unifying records with an incompatible field") {
    val rec1 = parser("{ field1: Int }")
    val rec2 = parser("{ field1: Str }")
    val result = unifier.unify(Substitution(), rec1, rec2)
    assert(result.isEmpty)
  }

  test("unifying variants with compatible fields") {
    val c = VarT1("c")
    val d = VarT1("d")
    val variant1 = parser("""Tag1({ field1: Int }) | c""")
    val variant2 = parser("""Tag2({ field2: Str }) | d""")
    val expectedSub = Substitution(
        EqClass(Set(c.no)) -> parser("""(| Tag2: { field2: Str } | a100 |)"""),
        EqClass(Set(d.no)) -> parser("""(| Tag1: { field1: Int } | a100 |)"""),
        EqClass(Set(FIRST_VAR)) -> VarT1(FIRST_VAR),
    ) ///
    val result = unifier.unify(Substitution(), variant1, variant2)
    val expectedType = parser("""Tag1({ field1: Int }) | Tag2({ field2: Str }) | a100""")
    assert(result.contains((expectedSub, expectedType)))
  }

  test("unifying a variant with a variable") {
    val c = VarT1("c")
    val d = VarT1("d")
    val variant1 = parser("""Variant(c)""")
    val variant2 = parser("""Tag2({ field2: Str }) | d""")
    val expectedSub = Substitution(
        EqClass(Set(c.no)) -> parser("""(| Tag2: { field2: Str } | d |)"""),
        EqClass(Set(d.no)) -> d,
    ) ///
    val result = unifier.unify(Substitution(), variant1, variant2)
    val expectedType = parser("""Tag2({ field2: Str }) | d""")
    assert(result.contains((expectedSub, expectedType)))
  }

  test("unifying variants with different types assigned to the same key") {
    // ADR-014 requires the following test to fail.
    // However, we do not enforce that yet.
    val c = VarT1("c")
    val d = VarT1("d")
    val variant1 = parser("""Tag1({ field1: Int }) | c""")
    val variant2 = parser("""Tag2({ field1: Str }) | d""")
    val expectedSub = Substitution(
        EqClass(Set(c.no)) -> parser("""(| Tag2: { field1: Str } | a100 |)"""),
        EqClass(Set(d.no)) -> parser("""(| Tag1: { field1: Int } | a100 |)"""),
        EqClass(Set(FIRST_VAR)) -> VarT1(FIRST_VAR),
    ) ///
    val result = unifier.unify(Substitution(), variant1, variant2)
    val expectedType = parser("""Tag1({ field1: Int }) | Tag2({ field1: Str }) | a100""")
    assert(result.contains((expectedSub, expectedType)))
  }

  test("unifying variants with incompatible fields") {
    val variant1 = parser("""Tag1({ field1: Int })""")
    val variant2 = parser("""Tag2({ field2: Str })""")
    val result = unifier.unify(Substitution(), variant1, variant2)
    assert(result.isEmpty)
  }

  // regression
  test("merge equivalence classes of a -> b, b -> a") {
    val expectedSub = Substitution(EqClass(Set(0, 1)) -> VarT1(0))
    val result = unifier.unify(Substitution(EqClass(0) -> VarT1("b"), EqClass(1) -> VarT1("a")), VarT1("a"), VarT1("b"))
    assert(result.contains((expectedSub, VarT1(0))))
  }

  // regression
  test("no stack overflow #925") {
    val oper1 = OperT1(Seq(VarT1("a")), RecT1("f" -> VarT1("a")))
    val oper2 = OperT1(Seq(VarT1("a")), RecT1("f" -> SetT1(VarT1("a"))))
    assert(unifier.unify(Substitution(), oper1, oper2).isEmpty)
  }
}
