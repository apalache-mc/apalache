package at.forsyte.apalache.io.itf

import at.forsyte.apalache.io.json.ujsonimpl.{UJsonRep, ScalaFromUJsonAdapter}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestItfJsonToTla extends AnyFunSuite {

  val itfToTla = new ItfJsonToTla(ScalaFromUJsonAdapter)

  import ujson._

  test("parseHeaderAndVarTypes on empty input") {
    val empty = UJsonRep(Obj())
    assert(itfToTla.parseHeaderAndVarTypes(empty).isLeft, "expected failure on empty input")
  }

  test("parseHeaderAndVarTypes on missing vars field") {
    val metaEmpty = UJsonRep(Obj(META_FIELD -> Obj()))
    assert(itfToTla.parseHeaderAndVarTypes(metaEmpty).isLeft, "expected failure on missing vars field")
  }

  test("parseHeaderAndVarTypes on var types field that is not an object") {
    val typesNotObj = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD -> 42
              ),
            VARS_FIELD -> Arr(),
        )
    )
    assert(itfToTla.parseHeaderAndVarTypes(typesNotObj).isLeft,
        "expected failure on var types field that is not an object")
  }

  test("parseHeaderAndVarTypes on empty vars array") {
    val noVars = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD ->
                    Obj(
                        "x" -> "Int"
                    )
              ),
            VARS_FIELD ->
              Arr(), // empty
        )
    )
    assert(itfToTla.parseHeaderAndVarTypes(noVars).isLeft, "expected failure on empty vars array")
  }

  test("parseHeaderAndVarTypes on missing types mapping") {
    val noTypes = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD -> Obj() // empty
              ),
            VARS_FIELD -> Arr("x"),
        )
    )

    assert(itfToTla.parseHeaderAndVarTypes(noTypes).isLeft, "expected failure on missing the types mapping")
  }

  test("parseHeaderAndVarTypes on correct input") {
    val correct = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD ->
                    Obj(
                        "x" -> "Int",
                        "y" -> "Str -> Bool",
                    )
              ),
            VARS_FIELD -> Arr("x", "y"),
        )
    )

    assert(
        itfToTla
          .parseHeaderAndVarTypes(correct)
          .contains(
              Map(
                  "x" -> IntT1,
                  "y" -> FunT1(StrT1, BoolT1),
              )
          ),
        "expected success on correct input",
    )
  }

  test("attemptUnserializable") {
    val emptyObject = UJsonRep(Obj())
    assert(itfToTla.attemptUnserializable(emptyObject).isEmpty, "expected None on empty object")
  }

  test("attemptUnserializable on bogus unserializable values") {
    def unserializable(v: String): UJsonRep = UJsonRep(
        Obj(
            UNSERIALIZABLE_FIELD -> v
        )
    )

    val emptyString = unserializable("") // illegal identifier
    assert(
        itfToTla.attemptUnserializable(emptyString).exists(_.isLeft),
        "expected error on bogus unserializable value",
    )

    assert(
        itfToTla.attemptUnserializable(unserializable("Int")).exists(_.isLeft),
        "expected error on unserializable Int",
    )

    assert(
        itfToTla.attemptUnserializable(unserializable("Nat")).exists(_.isLeft),
        "expected error on unserializable Nat",
    )
  }

  test("parseItfValueToTlaExpr - BoolT1") {
    val tru = UJsonRep(Bool(true))

    assert(
        itfToTla.parseItfValueToTlaExpr(tru, IntT1).isLeft,
        "expected error when parsing boolean value with IntT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(tru, BoolT1).map(_.build).contains(tla.bool(true).build),
        "expected successful parsing of boolean value with BoolT1 type",
    )

  }

  test("parseItfValueToTlaExpr - StrT1") {
    val cake = UJsonRep(Str("cake"))

    assert(
        itfToTla.parseItfValueToTlaExpr(cake, IntT1).isLeft,
        "expected error when parsing string value with IntT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(cake, ConstT1("X")).isLeft,
        "expected error when parsing string value with ConstT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(cake, StrT1).map(_.build).contains(tla.str("cake").build),
        "expected successful parsing of string value with StrT1 type",
    )
  }

  test("parseItfValueToTlaExpr - ConstT1") {
    val oneOfA = UJsonRep(Str("1_OF_A"))

    assert(
        itfToTla.parseItfValueToTlaExpr(oneOfA, StrT1).isLeft,
        "expected error when parsing const value with StrT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(oneOfA, ConstT1("B")).isLeft,
        "expected error when parsing const value with mismatched ConstT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(oneOfA, ConstT1("A")).map(_.build).contains(tla.const("1", ConstT1("A")).build),
        "expected successful parsing of const value with matching ConstT1 type",
    )
  }

  private val one: UJsonRep = UJsonRep(Num(1))

  test("parseItfValueToTlaExpr - intT1") {
    assert(
        itfToTla.parseItfValueToTlaExpr(one, StrT1).isLeft,
        "expected error when parsing integer value with StrT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(one, IntT1).map(_.build).contains(tla.int(1).build),
        "expected successful parsing of integer value with IntT1 type",
    )

    val bigOne = UJsonRep(Obj(BIG_INT_FIELD -> "1"))

    assert(
        itfToTla.parseItfValueToTlaExpr(bigOne, StrT1).isLeft,
        "expected error when parsing big integer value with StrT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(bigOne, IntT1).map(_.build).contains(tla.int(1).build),
        "expected successful parsing of big integer value with IntT1 type",
    )
  }

  test("parseItfValueToTlaExpr - SeqT1") {
    val emptySeq = UJsonRep(Arr())

    assert(
        itfToTla.parseItfValueToTlaExpr(emptySeq, FunT1(IntT1, IntT1)).isLeft,
        "expected error when parsing empty array with FunT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(emptySeq, SeqT1(IntT1)).map(_.build).contains(tla.emptySeq(IntT1).build),
        "expected successful parsing of empty array as SeqT1(IntT1)",
    )
    assert(
        itfToTla.parseItfValueToTlaExpr(emptySeq, SeqT1(StrT1)).map(_.build).contains(tla.emptySeq(StrT1).build),
        "expected successful parsing of empty array as SeqT1(StrT1)",
    )

    val tt = FunT1(RecT1("x" -> SetT1(BoolT1)), SeqT1(TupT1(ConstT1("X"))))
    assert(
        itfToTla.parseItfValueToTlaExpr(emptySeq, SeqT1(tt)).map(_.build).contains(tla.emptySeq(tt).build),
        "expected successful parsing of empty array as SeqT1 with complex type",
    )

    val oneTwoThree = UJsonRep(Arr(1, 2, 3))

    assert(
        itfToTla.parseItfValueToTlaExpr(oneTwoThree, FunT1(IntT1, IntT1)).isLeft,
        "expected error when parsing integer array with FunT1 type",
    )

    assert(
        itfToTla
          .parseItfValueToTlaExpr(oneTwoThree, SeqT1(IntT1))
          .map(_.build)
          .contains(tla
                .seq(Seq[BigInt](1, 2, 3).map(tla.int): _*)
                .build),
        "expected successful parsing of integer array as SeqT1(IntT1)",
    )
  }

  test("parseItfValueToTlaExpr - RecT1") {
    val emptyRec = UJsonRep(Obj())

    assert(
        itfToTla.parseItfValueToTlaExpr(emptyRec, RecT1()).isLeft,
        "expected error when parsing empty object as empty RecT1",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(emptyRec, RecT1("x" -> IntT1)).isLeft,
        "expected error when parsing empty object with non-empty RecT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(emptyRec, SeqT1(IntT1)).isLeft,
        "expected error when parsing empty object with SeqT1 type",
    )

    val xyRec = UJsonRep(
        Obj(
            "x" -> 1,
            "y" -> "abc",
        )
    )
    val xyRecT = RecT1("x" -> IntT1, "y" -> StrT1)

    assert(
        itfToTla.parseItfValueToTlaExpr(xyRec, IntT1).isLeft,
        "expected error when parsing record with IntT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(xyRec, RecT1()).isLeft,
        "expected error when parsing record with empty RecT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(xyRec, RecT1("x" -> IntT1, "y" -> StrT1, "z" -> IntT1)).isLeft,
        "expected error when parsing record with mismatched RecT1 type (extra field)",
    )

    assert(
        itfToTla
          .parseItfValueToTlaExpr(xyRec, xyRecT)
          .map(_.build)
          .contains(tla
                .rec(
                    "x" -> tla.int(1),
                    "y" -> tla.str("abc"),
                )
                .build),
        "expected successful parsing of record with matching RecT1 type",
    )
  }

  test("parseItfValueToTlaExpr - TupT1") {
    val tupOneA = UJsonRep(
        Obj(
            TUP_FIELD ->
              Arr(1, "A")
        )
    )

    val tupT = TupT1(IntT1, StrT1)

    assert(
        itfToTla.parseItfValueToTlaExpr(one, tupT).isLeft,
        "expected error when parsing integer value with TupT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(tupOneA, SetT1(IntT1)).isLeft,
        "expected error when parsing tuple with SetT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(tupOneA, TupT1()).isLeft,
        "expected error when parsing tuple with empty TupT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(tupOneA, TupT1(IntT1, StrT1, BoolT1)).isLeft,
        "expected error when parsing tuple with mismatched TupT1 type (wrong arity)",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(tupOneA, tupT).map(_.build).contains(tla.tuple(tla.int(1), tla.str("A")).build),
        "expected successful parsing of tuple with matching TupT1 type",
    )
  }

  test("parseItfValueToTlaExpr - SetT1") {
    val emptySet = UJsonRep(Obj(SET_FIELD -> Arr()))

    val setT = SetT1(BoolT1)

    assert(
        itfToTla.parseItfValueToTlaExpr(one, setT).isLeft,
        "expected error when parsing integer value with SetT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(emptySet, IntT1).isLeft,
        "expected error when parsing set with IntT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(emptySet, setT).map(_.build).contains(tla.emptySet(setT.elem).build),
        "expected successful parsing of empty set with SetT1 type",
    )

    val boolSet = UJsonRep(Obj(SET_FIELD -> Arr(true, false)))

    assert(
        itfToTla.parseItfValueToTlaExpr(boolSet, SetT1(IntT1)).isLeft,
        "expected error when parsing boolean set with SetT1(IntT1) type",
    )

    assert(
        itfToTla
          .parseItfValueToTlaExpr(boolSet, setT)
          .map(_.build)
          .contains(tla.enumSet(tla.bool(true), tla.bool(false)).build),
        "expected successful parsing of boolean set with SetT1(BoolT1) type",
    )

    val junkSet = UJsonRep(Obj(
            SET_FIELD -> Arr(true, false),
            "foo" -> "bar",
        ))

    assert(
        itfToTla.parseItfValueToTlaExpr(junkSet, setT).isLeft,
        "expected error when parsing set with extra fields",
    )
  }

  test("parseItfValueToTlaExpr - FunT1") {
    val emptyFun = UJsonRep(Obj(MAP_FIELD -> Arr()))

    val funT = FunT1(IntT1, IntT1)

    assert(
        itfToTla.parseItfValueToTlaExpr(one, funT).isLeft,
        "expected error when parsing integer value with FunT1 type",
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(emptyFun, IntT1).isLeft,
        "expected error when parsing function with IntT1 type",
    )

    assert(
        itfToTla
          .parseItfValueToTlaExpr(emptyFun, funT)
          .map(_.build)
          .contains(tla
                .setAsFun(tla.emptySet(TupT1(funT.arg, funT.res)))
                .build),
        "expected successful parsing of empty function with FunT1 type",
    )

    val id12 = UJsonRep(
        Obj(MAP_FIELD ->
          Arr(Arr(1, 1), Arr(2, 2)))
    )

    assert(
        itfToTla.parseItfValueToTlaExpr(id12, FunT1(IntT1, StrT1)).isLeft,
        "expected error when parsing function with mismatched FunT1 result type",
    )

    assert(
        itfToTla
          .parseItfValueToTlaExpr(id12, funT)
          .map(_.build)
          .contains(tla
                .setAsFun(tla.enumSet(
                        Seq(1, 2).map { i => tla.tuple(tla.int(i), tla.int(i)) }: _*
                    ))
                .build),
        "expected successful parsing of identity function with FunT1 type",
    )
  }

  test("parseTrace") {
    val noStates = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD -> Obj("x" -> "Int")
              ),
            VARS_FIELD -> Arr("x"),
        )
    )

    assert(
        itfToTla.parseTrace(noStates).isLeft,
        "expected error when parsing trace without states field",
    )

    val malformedStates = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD -> Obj("x" -> "Int")
              ),
            VARS_FIELD -> Arr("x"),
            STATES_FIELD -> 2,
        )
    )

    assert(
        itfToTla.parseTrace(malformedStates).isLeft,
        "expected error when parsing trace with malformed states field",
    )

    val missingVar = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD -> Obj("x" -> "Int", "y" -> "Str")
              ),
            VARS_FIELD -> Arr("x", "y"),
            STATES_FIELD -> Arr(
                Obj(
                    "x" -> 1
                )
            ),
        )
    )

    assert(
        itfToTla.parseTrace(missingVar).isLeft,
        "expected error when parsing trace with missing variable in state",
    )

    val spuriousVar = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD -> Obj("x" -> "Int", "y" -> "Str")
              ),
            VARS_FIELD -> Arr("x", "y"),
            STATES_FIELD -> Arr(
                Obj(
                    "x" -> 1,
                    "y" -> "a",
                    "z" -> true,
                )
            ),
        )
    )

    assert(
        itfToTla.parseTrace(spuriousVar).isLeft,
        "expected error when parsing trace with spurious variable in state",
    )

    val correctEmpty = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD -> Obj("x" -> "Int", "y" -> "Str")
              ),
            VARS_FIELD -> Arr("x", "y"),
            STATES_FIELD -> Arr(),
        )
    )

    assert(
        itfToTla.parseTrace(correctEmpty).contains(IndexedSeq.empty),
        "expected successful parsing of trace with empty states array",
    )

    val correctLen2 = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD -> Obj("x" -> "Int", "y" -> "Str")
              ),
            VARS_FIELD -> Arr("x", "y"),
            STATES_FIELD -> Arr(
                Obj(
                    "x" -> 1,
                    "y" -> "a",
                ),
                Obj(
                    META_FIELD -> Obj(), // not all states need meta, and any state may have meta
                    "x" -> 2,
                    "y" -> "b",
                ),
            ),
        )
    )

    assert(
        itfToTla
          .parseTrace(correctLen2)
          .contains(IndexedSeq(
                  Map(
                      "x" -> tla.int(1).build,
                      "y" -> tla.str("a").build,
                  ),
                  Map(
                      "x" -> tla.int(2).build,
                      "y" -> tla.str("b").build,
                  ),
              )),
        "expected successful parsing of trace with two states",
    )
  }
}
