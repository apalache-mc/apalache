package org.apalache_mc.tla.jir

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.{ScopeUnsafeBuilder, ScopedBuilder, TBuilderTypeException}
import org.scalatest.funsuite.AnyFunSuite

import java.math.BigInteger

/** Verifies the complete facade surface, Java-oriented factories, and behavior against the Scala implementation. */
class TestJavaFacade extends AnyFunSuite {
  test("checked and scope-unsafe facades produce the same IR as their Scala builders") {
    val checked = new TlaCheckedBuilder()
    val checkedExpression = checked.eql(
        checked.plus(checked.integer(40), checked.integer(BigInteger.valueOf(2))),
        checked.integer(42),
    )

    val scalaChecked = new ScopedBuilder()
    val expectedChecked: TlaEx = scalaChecked.eql(
        scalaChecked.plus(scalaChecked.int(40), scalaChecked.int(2)),
        scalaChecked.int(42),
    )
    assert(checked.build(checkedExpression) == expectedChecked)

    val unchecked = new TlaTypedScopeUncheckedBuilder()
    val actualUnchecked = unchecked.eql(
        unchecked.plus(unchecked.integer(40), unchecked.integer(2)),
        unchecked.integer(42),
    )
    val scalaUnchecked = new ScopeUnsafeBuilder()
    val expectedUnchecked = scalaUnchecked.eql(
        scalaUnchecked.plus(scalaUnchecked.int(40), scalaUnchecked.int(2)),
        scalaUnchecked.int(42),
    )
    assert(actualUnchecked == expectedUnchecked)
  }

  test("type and declaration factories produce the expected IR values") {
    assert(TlaTypes.INT == IntT1)
    assert(TlaTypes.REAL == RealT1)
    assert(TlaTypes.BOOL == BoolT1)
    assert(TlaTypes.STRING == StrT1)
    assert(TlaTypes.constant("PROCESS") == ConstT1("PROCESS"))
    assert(TlaTypes.typeVariable(0) == VarT1(0))
    assert(TlaTypes.typeVariable("b") == VarT1(1))
    assert(TlaTypes.function(TlaTypes.INT, TlaTypes.BOOL) == FunT1(IntT1, BoolT1))
    assert(TlaTypes.set(TlaTypes.INT) == SetT1(IntT1))
    assert(TlaTypes.sequence(TlaTypes.STRING) == SeqT1(StrT1))
    assert(TlaTypes.tuple(TlaTypes.INT, TlaTypes.BOOL) == TupT1(IntT1, BoolT1))
    assert(TlaTypes.sparseTuple(new IndexedType(2, TlaTypes.BOOL)) == SparseTupT1(2 -> BoolT1))
    assert(TlaTypes.operator(TlaTypes.BOOL, TlaTypes.INT) == OperT1(Seq(IntT1), BoolT1))
    assert(TlaTypes.row(new NamedType("n", TlaTypes.INT)) == RowT1("n" -> IntT1))
    assert(TlaTypes.row("a", new NamedType("n", TlaTypes.INT)) == RowT1(VarT1(0), "n" -> IntT1))
    assert(TlaTypes.rowRecord(new NamedType("n", TlaTypes.INT)) == RecRowT1(RowT1("n" -> IntT1)))
    assert(
        TlaTypes.rowRecord("a", new NamedType("n", TlaTypes.INT)) == RecRowT1(RowT1(VarT1(0), "n" -> IntT1))
    )
    assert(TlaTypes.variant(new NamedType("Some", TlaTypes.INT)) == VariantT1(RowT1("Some" -> IntT1)))
    assert(
        TlaTypes.variant("a", new NamedType("Some", TlaTypes.INT)) == VariantT1(
            RowT1(VarT1(0), "Some" -> IntT1)
        )
    )

    assert(TlaDeclarations.constant("N", TlaTypes.INT) == TlaConstDecl("N")(Typed(IntT1)))
    assert(TlaDeclarations.variable("x", TlaTypes.BOOL) == TlaVarDecl("x")(Typed(BoolT1)))
  }

  test("Java-friendly inputs build typed maps, records, CASE expressions, and EXCEPT updates") {
    val builder = new TlaCheckedBuilder()
    val x = builder.name("x", TlaTypes.INT)
    val one = builder.integer(1)
    val two = builder.integer(2)
    val set = builder.enumSet(one, two)

    val mapped = builder.map(x, new ExpressionPair(x, set))
    assert(builder.build(mapped).typeTag == Typed(SetT1(IntT1)))

    val record = builder.record(new NamedExpression("value", one))
    assert(builder.build(record).typeTag == Typed(RecRowT1(RowT1("value" -> IntT1))))

    val caseExpression = builder.caseOther(two, new ExpressionPair(builder.bool(true), one))
    assert(builder.build(caseExpression).typeTag == Typed(IntT1))

    val tuple = builder.tuple(one, two)
    val updated = builder.exceptMany(tuple, new ExceptUpdate(one, two))
    assert(builder.build(updated).typeTag == Typed(TupT1(IntT1, IntT1)))
  }

  test("checked operator declarations build to correctly typed IR") {
    val builder = new TlaCheckedBuilder()
    val parameter = builder.param("x", TlaTypes.INT)
    val body = builder.plus(builder.name("x", TlaTypes.INT), builder.integer(1))
    val declaration = builder.decl("Inc", body, parameter)
    val built = builder.build(declaration)

    assert(built.name == "Inc")
    assert(built.formalParams == List(OperParam("x")))
    assert(built.typeTag == Typed(OperT1(Seq(IntT1), IntT1)))
  }

  test("checked failures retain their causes while the scope-unsafe facade permits name clashes") {
    val builder = new TlaCheckedBuilder()
    val illTyped = builder.plus(builder.integer(1), builder.bool(true))
    val typeException = intercept[TlaBuilderTypeException](builder.build(illTyped))
    assert(typeException.getCause.isInstanceOf[TBuilderTypeException])

    val scopeClash = builder.tuple(
        builder.name("x", TlaTypes.INT),
        builder.name("x", TlaTypes.BOOL),
    )
    val scopeException = intercept[TlaBuilderScopeException](builder.build(scopeClash))
    assert(scopeException.getCause.getClass.getSimpleName == "TBuilderScopeException")

    val unchecked = new TlaTypedScopeUncheckedBuilder()
    val scopeUnchecked = unchecked.tuple(
        unchecked.name("x", TlaTypes.INT),
        unchecked.name("x", TlaTypes.BOOL),
    )
    assert(scopeUnchecked.typeTag == Typed(TupT1(IntT1, BoolT1)))
  }

  test("strict mode rejects invalid assignments while non-strict mode permits them") {
    val strict = new TlaTypedScopeUncheckedBuilder()
    intercept[IllegalArgumentException](strict.assign(strict.integer(1), strict.integer(2)))

    val nonStrict = new TlaTypedScopeUncheckedBuilder(false)
    assert(nonStrict.assign(nonStrict.integer(1), nonStrict.integer(2)).typeTag == Typed(BoolT1))
  }

  test("Java value records expose their components and value semantics") {
    val expressionPair = new ExpressionPair[String]("first", "second")
    val namedExpression = new NamedExpression[String]("field", "value")
    val exceptUpdate = new ExceptUpdate[String]("index", "value")
    val typedParameter = new TypedParameter("parameter", IntT1)
    val namedType = new NamedType("field", BoolT1)
    val indexedType = new IndexedType(2, StrT1)

    assert(expressionPair.first() == "first" && expressionPair.second() == "second")
    assert(namedExpression.name() == "field" && namedExpression.expression() == "value")
    assert(exceptUpdate.index() == "index" && exceptUpdate.value() == "value")
    assert(typedParameter.name() == "parameter" && typedParameter.`type`() == IntT1)
    assert(namedType.name() == "field" && namedType.`type`() == BoolT1)
    assert(indexedType.index() == 2 && indexedType.`type`() == StrT1)

    Seq[(AnyRef, AnyRef)](
        expressionPair -> new ExpressionPair[String]("first", "second"),
        namedExpression -> new NamedExpression[String]("field", "value"),
        exceptUpdate -> new ExceptUpdate[String]("index", "value"),
        typedParameter -> new TypedParameter("parameter", IntT1),
        namedType -> new NamedType("field", BoolT1),
        indexedType -> new IndexedType(2, StrT1),
    ).foreach { case (value, equalValue) =>
      assert(value == equalValue)
      assert(value.hashCode() == equalValue.hashCode())
      assert(value.toString.nonEmpty)
    }
  }

  test("every checked facade overload accepts a representative invocation") {
    BuilderMethodCoverage.exercise(new TlaCheckedBuilder(false))
  }

  test("every scope-unsafe facade overload accepts a representative invocation") {
    BuilderMethodCoverage.exercise(new TlaTypedScopeUncheckedBuilder(false))
  }
}
