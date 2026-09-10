package org.apalache_mc.tla.jir

import at.forsyte.apalache.tla.lir._
import org.scalatest.funsuite.AnyFunSuite

import scala.jdk.CollectionConverters._

class TestFacadeOperations extends AnyFunSuite {
  test("untyped and inconsistent declaration tags fail explicitly") {
    intercept[TlaBuilderTypeException](TlaTypes.typeOf(NameEx("x")(Untyped)))
    intercept[TlaBuilderTypeException](TlaTypes.typeOf(TlaVarDecl("x")(Untyped)))
    val wrongCount =
      TlaOperDecl("Op", List(OperParam("x")), ValEx(values.TlaInt(1))(Typed(IntT1)))(Typed(OperT1(Seq.empty, IntT1)))
    intercept[TlaBuilderTypeException](TlaDeclarations.parameters(wrongCount))
    val wrongArity = wrongCount.copy()(Typed(OperT1(Seq(OperT1(Seq(IntT1), IntT1)), IntT1)))
    intercept[TlaBuilderTypeException](TlaDeclarations.parameters(wrongArity))
    assert(TlaTypes.children(RecT1("z" -> IntT1, "a" -> BoolT1)).asScala.toSeq == Seq(BoolT1, IntT1))
  }

  test("structural operations retain generic tags, higher-order arity and recursion flags") {
    val signature = OperT1(Seq(OperT1(Seq(VarT1(7)), VarT1(7))), VarT1(7))
    val decl = TlaOperDecl("Op", List(OperParam("f", 1)), NameEx("x")(Typed(VarT1(7))))(Typed(signature))
    decl.isRecursive = true
    val renamed = TlaDeclarations.withHeader(decl, "Renamed", java.util.List.of("g"))
    val copied = TlaDeclarations.deepCopy(decl)
    val rewritten = TlaDeclarations.rewrite(decl, java.util.function.UnaryOperator.identity[TlaEx]())
    Seq(renamed, copied, rewritten).foreach { d =>
      assert(d.isRecursive)
      assert(d.typeTag == decl.typeTag)
      assert(d.formalParams.head.arity == 1)
      assert(d ne decl)
    }
    copied.body = ValEx(values.TlaInt(2))(Typed(IntT1))
    assert(decl.body.isInstanceOf[NameEx])
    assert(TlaExpressions.deepCopy(NullEx) eq NullEx)
  }

  test("unification reserves substitution domains and ranges and rejects exhausted pools") {
    val a = TlaTypes.typeVariable(0)
    val b = TlaTypes.typeVariable(1)
    val left = TlaTypes.rowRecord(a, new NamedType("x", TlaTypes.INT))
    val right = TlaTypes.rowRecord(b, new NamedType("y", TlaTypes.BOOL))
    val initial = TlaTypeSubstitution.of(java.util.Map.of[Integer, TlaType1](501, TlaTypes.typeVariable(900)))
    val unified = new TlaTypeUnifier().unify(java.util.Optional.of(initial), left, right).orElseThrow()
    assert(TlaTypes.usedVariables(unified.unifiedType()).asScala.forall(_.intValue > 900))
    assert(initial.applyOnce(TlaTypes.typeVariable(501)) == TlaTypes.typeVariable(900))
    val exhausted = new TlaTypeUnifier(TlaTypes.typeVariable(Int.MaxValue - 1))
    intercept[IllegalArgumentException](exhausted.unify(java.util.Optional.empty(), left, right))
    intercept[IllegalArgumentException](TlaTypeSubstitution.of(java.util.Map.of[Integer, TlaType1](-1, IntT1)))
    val invalidRow = TlaTypeSubstitution.of(java.util.Map.of[Integer, TlaType1](0, IntT1))
    intercept[IllegalStateException](invalidRow.applyFully(left))
  }

  test("rewrites visit occurrences once and never traverse callback replacements") {
    val b = new TlaTypedScopeUncheckedBuilder()
    val leaf = b.integer(1)
    val ex = b.plus(leaf, leaf)
    var visits = 0
    val result = TlaExpressions.rewrite(ex,
        node => {
          visits += 1
          if (node eq leaf) b.plus(leaf, leaf) else node
        })
    assert(visits == 3)
    assert(result.isInstanceOf[OperEx])
    intercept[NullPointerException](TlaExpressions.rewrite(ex, _ => null))
  }
}
