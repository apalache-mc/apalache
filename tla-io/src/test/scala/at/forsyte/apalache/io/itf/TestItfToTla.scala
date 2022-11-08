package at.forsyte.apalache.io.itf

import at.forsyte.apalache.io.json.JsonDeserializationError
import at.forsyte.apalache.io.json.impl.{UJsonRep, UJsonScalaFactory}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestItfToTla extends AnyFunSuite {

  val itfToTla = new ItfToTla(UJsonScalaFactory)

  import ujson._

  test("validateShapeAndGetTypes") {

    val empty = UJsonRep(Obj())
    assertThrows[JsonDeserializationError] {
      itfToTla.validateShapeAndGetTypes(empty)
    }

    val metaEmpty = UJsonRep(Obj(ItfToTla.META_FIELD -> Obj()))
    assertThrows[JsonDeserializationError] {
      itfToTla.validateShapeAndGetTypes(metaEmpty)
    }

    val noVars = UJsonRep(
        Obj(
            ItfToTla.META_FIELD ->
              Obj(
                  ItfToTla.VAR_TYPES_FIELD ->
                    Obj(
                        "x" -> "Int"
                    )
              ),
            ItfToTla.VARS_FIELD ->
              Arr(), // empty
        )
    )

    assertThrows[JsonDeserializationError] {
      itfToTla.validateShapeAndGetTypes(noVars)
    }

    val noTypes = UJsonRep(
        Obj(
            ItfToTla.META_FIELD ->
              Obj(
                  ItfToTla.VAR_TYPES_FIELD -> Obj() // empty
              ),
            ItfToTla.VARS_FIELD -> Arr("x"),
        )
    )

    assertThrows[JsonDeserializationError] {
      itfToTla.validateShapeAndGetTypes(noTypes)
    }

    val correct = UJsonRep(
        Obj(
            ItfToTla.META_FIELD ->
              Obj(
                  ItfToTla.VAR_TYPES_FIELD ->
                    Obj(
                        "x" -> "Int",
                        "y" -> "Str -> Bool",
                    )
              ),
            ItfToTla.VARS_FIELD -> Arr("x", "y"),
        )
    )

    assert(
        itfToTla.validateShapeAndGetTypes(correct) ==
          Map(
              "x" -> IntT1,
              "y" -> FunT1(StrT1, BoolT1),
          )
    )

  }

  test("attemptUnserializable") {

    val notUS = UJsonRep(Obj())

    assert(itfToTla.attemptUnserializable(notUS).isEmpty)

    def singleUS(v: String): UJsonRep = UJsonRep(
        Obj(
            ItfToTla.UNSERIALIZABLE_FIELD -> v
        )
    )

    val bogusUS = singleUS("") // illegal identifier

    assertThrows[JsonDeserializationError] {
      itfToTla.attemptUnserializable(bogusUS)
    }

    val int = singleUS("Int")

    assertThrows[JsonDeserializationError] {
      itfToTla.attemptUnserializable(int)
    }

    val nat = singleUS("Nat")

    assertThrows[JsonDeserializationError] {
      itfToTla.attemptUnserializable(nat)
    }
  }

  test("typeDrivenBuild") {

    // case BoolT1 =>

    val tru = UJsonRep(Bool(true))

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(tru, IntT1)
    }

    assert(itfToTla.typeDrivenBuild(tru, BoolT1).build == tla.bool(true).build)

    // case StrT1 =>

    val cake = UJsonRep(Str("cake"))

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(cake, IntT1)
    }

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(cake, ConstT1("X"))
    }

    assert(itfToTla.typeDrivenBuild(cake, StrT1).build == tla.str("cake").build)

    // case ct: ConstT1 =>

    val oneOfA = UJsonRep(Str("1_OF_A"))

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(oneOfA, StrT1)
    }

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(oneOfA, ConstT1("B"))
    }

    assert(itfToTla.typeDrivenBuild(oneOfA, ConstT1("A")).build == tla.const("1", ConstT1("A")).build)

    // case IntT1 =>

    val one = UJsonRep(Num(1))

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(one, StrT1)
    }

    assert(itfToTla.typeDrivenBuild(one, IntT1).build == tla.int(1).build)

    val bigOne = UJsonRep(Obj(ItfToTla.BIG_INT_FIELD -> "1"))

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(bigOne, StrT1)
    }

    assert(itfToTla.typeDrivenBuild(bigOne, IntT1).build == tla.int(1).build)

    // case SeqT1(elemT) =>

    val emptySeq = UJsonRep(Arr())

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(emptySeq, FunT1(IntT1, IntT1))
    }

    assert(itfToTla.typeDrivenBuild(emptySeq, SeqT1(IntT1)).build == tla.emptySeq(IntT1).build)
    assert(itfToTla.typeDrivenBuild(emptySeq, SeqT1(StrT1)).build == tla.emptySeq(StrT1).build)

    val tt = FunT1(RecT1("x" -> SetT1(BoolT1)), SeqT1(TupT1(ConstT1("X"))))
    assert(itfToTla.typeDrivenBuild(emptySeq, SeqT1(tt)).build == tla.emptySeq(tt).build)

    val oneTwoThree = UJsonRep(Arr(1, 2, 3))

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(oneTwoThree, FunT1(IntT1, IntT1))
    }

    assert(itfToTla.typeDrivenBuild(oneTwoThree, SeqT1(IntT1)).build == tla
      .seq(Seq[BigInt](1, 2, 3).map(tla.int): _*)
      .build)

    // case RecT1(fieldTypes) =>

    val emptyRec = UJsonRep(Obj())

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(emptyRec, RecT1())
    }

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(emptyRec, RecT1("x" -> IntT1))
    }

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(emptyRec, SeqT1(IntT1))
    }

    val xyRec = UJsonRep(
        Obj(
            "x" -> 1,
            "y" -> "abc",
        )
    )
    val xyRecT = RecT1("x" -> IntT1, "y" -> StrT1)

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(xyRec, IntT1)
    }

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(xyRec, RecT1())
    }

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(xyRec, RecT1("x" -> IntT1, "y" -> StrT1, "z" -> IntT1))
    }

    assert(itfToTla.typeDrivenBuild(xyRec, xyRecT).build == tla
      .rec(
          "x" -> tla.int(1),
          "y" -> tla.str("abc"),
      )
      .build)

    // case TupT1(elems @ _*) =>

    val tupOneA = UJsonRep(
        Obj(
            ItfToTla.TUP_FIELD ->
              Arr(1, "A")
        )
    )

    val tupT = TupT1(IntT1, StrT1)

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(one, tupT)
    }

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(tupOneA, SetT1(IntT1))
    }

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(tupOneA, TupT1())
    }

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(tupOneA, TupT1(IntT1, StrT1, BoolT1))
    }

    assert(itfToTla.typeDrivenBuild(tupOneA, tupT).build == tla.tuple(tla.int(1), tla.str("A")).build)

    // case SetT1(elemT) =>

    val emptySet = UJsonRep(Obj(ItfToTla.SET_FIELD -> Arr()))

    val setT = SetT1(BoolT1)

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(one, setT)
    }

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(emptySet, IntT1)
    }

    assert(itfToTla.typeDrivenBuild(emptySet, setT).build == tla.emptySet(setT.elem).build)

    val boolSet = UJsonRep(Obj(ItfToTla.SET_FIELD -> Arr(true, false)))

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(boolSet, SetT1(IntT1))
    }

    assert(itfToTla.typeDrivenBuild(boolSet, setT).build == tla.enumSet(tla.bool(true), tla.bool(false)).build)

    // case FunT1(argT, resT) =>

    val emptyFun = UJsonRep(Obj(ItfToTla.MAP_FIELD -> Arr()))

    val funT = FunT1(IntT1, IntT1)

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(one, funT)
    }

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(emptyFun, IntT1)
    }

    assert(itfToTla.typeDrivenBuild(emptyFun, funT).build == tla
      .setAsFun(tla.emptySet(TupT1(funT.arg, funT.res)))
      .build)

    val id12 = UJsonRep(
        Obj(ItfToTla.MAP_FIELD ->
          Arr(Arr(1, 1), Arr(2, 2)))
    )

    assertThrows[JsonDeserializationError] {
      itfToTla.typeDrivenBuild(id12, FunT1(IntT1, StrT1))
    }

    assert(itfToTla.typeDrivenBuild(id12, funT).build == tla
      .setAsFun(tla.enumSet(
              Seq(1, 2).map { i => tla.tuple(tla.int(i), tla.int(i)) }: _*
          ))
      .build)

  }

  test("getTrace") {
    val noStates = UJsonRep(
        Obj(
            ItfToTla.META_FIELD ->
              Obj(
                  ItfToTla.VAR_TYPES_FIELD -> Obj("x" -> "Int")
              ),
            ItfToTla.VARS_FIELD -> Arr("x"),
        )
    )

    assertThrows[JsonDeserializationError] {
      itfToTla.getTrace(noStates)
    }

    val malformedStates = UJsonRep(
        Obj(
            ItfToTla.META_FIELD ->
              Obj(
                  ItfToTla.VAR_TYPES_FIELD -> Obj("x" -> "Int")
              ),
            ItfToTla.VARS_FIELD -> Arr("x"),
            ItfToTla.STATES_FIELD -> 2,
        )
    )

    assertThrows[JsonDeserializationError] {
      itfToTla.getTrace(malformedStates)
    }

    val missingVar = UJsonRep(
        Obj(
            ItfToTla.META_FIELD ->
              Obj(
                  ItfToTla.VAR_TYPES_FIELD -> Obj("x" -> "Int", "y" -> "Str")
              ),
            ItfToTla.VARS_FIELD -> Arr("x", "y"),
            ItfToTla.STATES_FIELD -> Arr(
                Obj(
                    "x" -> 1
                )
            ),
        )
    )

    assertThrows[JsonDeserializationError] {
      itfToTla.getTrace(missingVar)
    }

    val spuriousVar = UJsonRep(
        Obj(
            ItfToTla.META_FIELD ->
              Obj(
                  ItfToTla.VAR_TYPES_FIELD -> Obj("x" -> "Int", "y" -> "Str")
              ),
            ItfToTla.VARS_FIELD -> Arr("x", "y"),
            ItfToTla.STATES_FIELD -> Arr(
                Obj(
                    "x" -> 1,
                    "y" -> "a",
                    "z" -> true,
                )
            ),
        )
    )

    assertThrows[JsonDeserializationError] {
      itfToTla.getTrace(spuriousVar)
    }

    val correctEmpty = UJsonRep(
        Obj(
            ItfToTla.META_FIELD ->
              Obj(
                  ItfToTla.VAR_TYPES_FIELD -> Obj("x" -> "Int", "y" -> "Str")
              ),
            ItfToTla.VARS_FIELD -> Arr("x", "y"),
            ItfToTla.STATES_FIELD -> Arr(),
        )
    )

    assert(itfToTla.getTrace(correctEmpty) == IndexedSeq.empty)

    val correctLen2 = UJsonRep(
        Obj(
            ItfToTla.META_FIELD ->
              Obj(
                  ItfToTla.VAR_TYPES_FIELD -> Obj("x" -> "Int", "y" -> "Str")
              ),
            ItfToTla.VARS_FIELD -> Arr("x", "y"),
            ItfToTla.STATES_FIELD -> Arr(
                Obj(
                    "x" -> 1,
                    "y" -> "a",
                ),
                Obj(
                    ItfToTla.META_FIELD -> Obj(), // not all states need meta, and any state may have meta
                    "x" -> 2,
                    "y" -> "b",
                ),
            ),
        )
    )

    assert(itfToTla.getTrace(correctLen2) == IndexedSeq(
        Map(
            "x" -> tla.int(1).build,
            "y" -> tla.str("a").build,
        ),
        Map(
            "x" -> tla.int(2).build,
            "y" -> tla.str("b").build,
        ),
    ))

  }

}
