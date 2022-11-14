package at.forsyte.apalache.io.itf

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
    assert {
      itfToTla.validateShapeAndGetTypes(empty).isLeft
    }

    val metaEmpty = UJsonRep(Obj(META_FIELD -> Obj()))
    assert {
      itfToTla.validateShapeAndGetTypes(metaEmpty).isLeft
    }

    val typesNotObj = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD -> 42
              ),
            VARS_FIELD -> Arr(),
        )
    )

    assert {
      itfToTla.validateShapeAndGetTypes(typesNotObj).isLeft
    }

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

    assert {
      itfToTla.validateShapeAndGetTypes(noVars).isLeft
    }

    val noTypes = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD -> Obj() // empty
              ),
            VARS_FIELD -> Arr("x"),
        )
    )

    assert {
      itfToTla.validateShapeAndGetTypes(noTypes).isLeft
    }

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

    assert {
      itfToTla
        .validateShapeAndGetTypes(correct)
        .contains(
            Map(
                "x" -> IntT1,
                "y" -> FunT1(StrT1, BoolT1),
            )
        )
    }

  }

  test("attemptUnserializable") {

    val notUS = UJsonRep(Obj())

    assert(itfToTla.attemptUnserializable(notUS).isEmpty)

    def singleUS(v: String): UJsonRep = UJsonRep(
        Obj(
            UNSERIALIZABLE_FIELD -> v
        )
    )

    val bogusUS = singleUS("") // illegal identifier

    assert {
      itfToTla.attemptUnserializable(bogusUS).exists(_.isLeft)
    }

    val int = singleUS("Int")

    assert {
      itfToTla.attemptUnserializable(int).exists(_.isLeft)
    }

    val nat = singleUS("Nat")

    assert {
      itfToTla.attemptUnserializable(nat).exists(_.isLeft)
    }
  }

  test("typeDrivenBuild - BoolT1") {

    val tru = UJsonRep(Bool(true))

    assert {
      itfToTla.typeDrivenBuild(tru, IntT1).isLeft
    }

    assert(itfToTla.typeDrivenBuild(tru, BoolT1).map(_.build).contains(tla.bool(true).build))

  }

  test("typeDrivenBuild - StrT1") {
    val cake = UJsonRep(Str("cake"))

    assert {
      itfToTla.typeDrivenBuild(cake, IntT1).isLeft
    }

    assert {
      itfToTla.typeDrivenBuild(cake, ConstT1("X")).isLeft
    }

    assert(itfToTla.typeDrivenBuild(cake, StrT1).map(_.build).contains(tla.str("cake").build))

  }

  test("typeDrivenBuild - ConstT1") {

    val oneOfA = UJsonRep(Str("1_OF_A"))

    assert {
      itfToTla.typeDrivenBuild(oneOfA, StrT1).isLeft
    }

    assert {
      itfToTla.typeDrivenBuild(oneOfA, ConstT1("B")).isLeft
    }

    assert(itfToTla.typeDrivenBuild(oneOfA, ConstT1("A")).map(_.build).contains(tla.const("1", ConstT1("A")).build))

  }

  private val one: UJsonRep = UJsonRep(Num(1))
  test("typeDrivenBuild - intT1") {
    assert {
      itfToTla.typeDrivenBuild(one, StrT1).isLeft
    }

    assert(itfToTla.typeDrivenBuild(one, IntT1).map(_.build).contains(tla.int(1).build))

    val bigOne = UJsonRep(Obj(BIG_INT_FIELD -> "1"))

    assert {
      itfToTla.typeDrivenBuild(bigOne, StrT1).isLeft
    }

    assert(itfToTla.typeDrivenBuild(bigOne, IntT1).map(_.build).contains(tla.int(1).build))

  }

  test("typeDrivenBuild - SeqT1") {
    val emptySeq = UJsonRep(Arr())

    assert {
      itfToTla.typeDrivenBuild(emptySeq, FunT1(IntT1, IntT1)).isLeft
    }

    assert(itfToTla.typeDrivenBuild(emptySeq, SeqT1(IntT1)).map(_.build).contains(tla.emptySeq(IntT1).build))
    assert(itfToTla.typeDrivenBuild(emptySeq, SeqT1(StrT1)).map(_.build).contains(tla.emptySeq(StrT1).build))

    val tt = FunT1(RecT1("x" -> SetT1(BoolT1)), SeqT1(TupT1(ConstT1("X"))))
    assert(itfToTla.typeDrivenBuild(emptySeq, SeqT1(tt)).map(_.build).contains(tla.emptySeq(tt).build))

    val oneTwoThree = UJsonRep(Arr(1, 2, 3))

    assert {
      itfToTla.typeDrivenBuild(oneTwoThree, FunT1(IntT1, IntT1)).isLeft
    }

    assert(itfToTla
          .typeDrivenBuild(oneTwoThree, SeqT1(IntT1))
          .map(_.build)
          .contains(tla
                .seq(Seq[BigInt](1, 2, 3).map(tla.int): _*)
                .build))
  }

  test("typeDrivenBuild - RecT1") {
    val emptyRec = UJsonRep(Obj())

    assert {
      itfToTla.typeDrivenBuild(emptyRec, RecT1()).isLeft
    }

    assert {
      itfToTla.typeDrivenBuild(emptyRec, RecT1("x" -> IntT1)).isLeft
    }

    assert {
      itfToTla.typeDrivenBuild(emptyRec, SeqT1(IntT1)).isLeft
    }

    val xyRec = UJsonRep(
        Obj(
            "x" -> 1,
            "y" -> "abc",
        )
    )
    val xyRecT = RecT1("x" -> IntT1, "y" -> StrT1)

    assert {
      itfToTla.typeDrivenBuild(xyRec, IntT1).isLeft
    }

    assert {
      itfToTla.typeDrivenBuild(xyRec, RecT1()).isLeft
    }

    assert {
      itfToTla.typeDrivenBuild(xyRec, RecT1("x" -> IntT1, "y" -> StrT1, "z" -> IntT1)).isLeft
    }

    assert(itfToTla
          .typeDrivenBuild(xyRec, xyRecT)
          .map(_.build)
          .contains(tla
                .rec(
                    "x" -> tla.int(1),
                    "y" -> tla.str("abc"),
                )
                .build))

  }

  test("typeDrivenBuild - TupT1") {
    val tupOneA = UJsonRep(
        Obj(
            TUP_FIELD ->
              Arr(1, "A")
        )
    )

    val tupT = TupT1(IntT1, StrT1)

    assert {
      itfToTla.typeDrivenBuild(one, tupT).isLeft
    }

    assert {
      itfToTla.typeDrivenBuild(tupOneA, SetT1(IntT1)).isLeft
    }

    assert {
      itfToTla.typeDrivenBuild(tupOneA, TupT1()).isLeft
    }

    assert {
      itfToTla.typeDrivenBuild(tupOneA, TupT1(IntT1, StrT1, BoolT1)).isLeft
    }

    assert(itfToTla.typeDrivenBuild(tupOneA, tupT).map(_.build).contains(tla.tuple(tla.int(1), tla.str("A")).build))

  }

  test("typeDrivenBuild - SetT1") {
    val emptySet = UJsonRep(Obj(SET_FIELD -> Arr()))

    val setT = SetT1(BoolT1)

    assert {
      itfToTla.typeDrivenBuild(one, setT).isLeft
    }

    assert {
      itfToTla.typeDrivenBuild(emptySet, IntT1).isLeft
    }

    assert(itfToTla.typeDrivenBuild(emptySet, setT).map(_.build).contains(tla.emptySet(setT.elem).build))

    val boolSet = UJsonRep(Obj(SET_FIELD -> Arr(true, false)))

    assert {
      itfToTla.typeDrivenBuild(boolSet, SetT1(IntT1)).isLeft
    }

    assert(itfToTla
          .typeDrivenBuild(boolSet, setT)
          .map(_.build)
          .contains(tla.enumSet(tla.bool(true), tla.bool(false)).build))

    val junkSet = UJsonRep(Obj(
            SET_FIELD -> Arr(true, false),
            "foo" -> "bar",
        ))

    assert {
      itfToTla.typeDrivenBuild(junkSet, setT).isLeft
    }

  }

  test("typeDrivenBuild - FunT1") {
    val emptyFun = UJsonRep(Obj(MAP_FIELD -> Arr()))

    val funT = FunT1(IntT1, IntT1)

    assert {
      itfToTla.typeDrivenBuild(one, funT).isLeft
    }

    assert {
      itfToTla.typeDrivenBuild(emptyFun, IntT1).isLeft
    }

    assert(itfToTla
          .typeDrivenBuild(emptyFun, funT)
          .map(_.build)
          .contains(tla
                .setAsFun(tla.emptySet(TupT1(funT.arg, funT.res)))
                .build))

    val id12 = UJsonRep(
        Obj(MAP_FIELD ->
          Arr(Arr(1, 1), Arr(2, 2)))
    )

    assert {
      itfToTla.typeDrivenBuild(id12, FunT1(IntT1, StrT1)).isLeft
    }

    assert(itfToTla
          .typeDrivenBuild(id12, funT)
          .map(_.build)
          .contains(tla
                .setAsFun(tla.enumSet(
                        Seq(1, 2).map { i => tla.tuple(tla.int(i), tla.int(i)) }: _*
                    ))
                .build))

  }

  test("getTrace") {
    val noStates = UJsonRep(
        Obj(
            META_FIELD ->
              Obj(
                  VAR_TYPES_FIELD -> Obj("x" -> "Int")
              ),
            VARS_FIELD -> Arr("x"),
        )
    )

    assert {
      itfToTla.getTrace(noStates).isLeft
    }

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

    assert {
      itfToTla.getTrace(malformedStates).isLeft
    }

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

    assert {
      itfToTla.getTrace(missingVar).isLeft
    }

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

    assert {
      itfToTla.getTrace(spuriousVar).isLeft
    }

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

    assert(itfToTla.getTrace(correctEmpty).contains(IndexedSeq.empty))

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

    assert(itfToTla
          .getTrace(correctLen2)
          .contains(IndexedSeq(
                  Map(
                      "x" -> tla.int(1).build,
                      "y" -> tla.str("a").build,
                  ),
                  Map(
                      "x" -> tla.int(2).build,
                      "y" -> tla.str("b").build,
                  ),
              )))

  }

}
