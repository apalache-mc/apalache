package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.io.UTFPrinter
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaFunOper, TlaSeqOper}
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir.convenience._

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs._

@RunWith(classOf[JUnitRunner])
class TestPrinter extends AnyFunSuite {
  val toUtf = UTFPrinter

  private def assertPrint(ex: TlaEx, expected: String): Unit = {
    assert(toUtf(ex) == expected)
  }

  private def assertDeclPrint(decl: TlaDecl, expected: String): Unit = {
    assert(toUtf(decl) == expected)
  }

  test("Test UTF8: literals and simple expressions") {
    assertPrint(NullEx, "<[NULL]>")
    assertPrint(tla.name("x"), "x")
    assertPrint(tla.int(42), "42")
    assertPrint(tla.bigInt(BigInt("9223372036854775808")), "9223372036854775808")
    assertPrint(tla.decimal(BigDecimal("3.14")), "3.14")
    assertPrint(tla.str("hello"), "\"hello\"")
    assertPrint(tla.bool(true), "TRUE")
    assertPrint(tla.bool(false), "FALSE")
    assertPrint(tla.booleanSet(), "BOOLEAN")
    assertPrint(tla.stringSet(), "STRING")
    assertPrint(tla.intSet(), "Int")
    assertPrint(tla.natSet(), "Nat")
    assertPrint(ValEx(TlaRealSet), "Real")
    assertPrint(ValEx(TlaRealInfinity), "Infinity")

    val decl = TlaOperDecl("c", List(), tla.int(1))
    assertPrint(tla.letIn(tla.appOp(tla.name("c")), decl), "LET c ≜ 1 IN c()")
    assert(toUtf(tla.plus(tla.name("a"), tla.name("b")), p_rmSpace = true) == "a+b")
  }

  test("Test UTF8: TlaOper") {
    val S = tla.name("S")
    val T = tla.name("T")
    val a = tla.name("a")
    val b = tla.name("b")
    val c = tla.name("c")
    val d = tla.name("d")
    val e = tla.name("e")
    val p = tla.name("p")
    val q = tla.name("q")
    val x = tla.name("x")

    val eqEx1: String = toUtf(tla.eql(a, b))
    val eqEx2: String = toUtf(tla.eql(tla.plus(a, b), tla.minus(c, d)))

    assert(eqEx1 == "a = b")
    assert(eqEx2 == "(a + b) = (c - d)")

    val neEx1: String = toUtf(tla.neql(a, b))
    val neEx2: String = toUtf(tla.neql(tla.plus(a, b), tla.minus(c, d)))

    assert(neEx1 == "a %s b".format(toUtf.m_neq))
    assert(neEx2 == "(a + b) %s (c - d)".format(toUtf.m_neq))

    val appEx1: String = toUtf(tla.appOp(x))
    val appEx2: String = toUtf(tla.appOp(x, a))
    val appEx3: String = toUtf(tla.appOp(x, a, b, c))
    val appEx4: String = toUtf(tla.appOp(a, tla.appOp(b)))
    val appEx5: String = toUtf(tla.appOp(a, tla.appOp(b, c), tla.appOp(d, e)))

    assert(appEx1 == "x()")
    assert(appEx2 == "x(a)")
    assert(appEx3 == "x(a, b, c)")
    assert(appEx4 == "a(b())")
    assert(appEx5 == "a(b(c), d(e))")

    val chooseEx1: String = toUtf(tla.choose(x, p))
    val chooseEx2: String = toUtf(tla.choose(x, S, p))
    val chooseEx3: String = toUtf(tla.choose(x, tla.and(p, q)))
    val chooseEx4: String = toUtf(tla.choose(x, tla.times(S, T), tla.and(p, q)))

    assert(chooseEx1 == "CHOOSE x : p")
    assert(chooseEx2 == "CHOOSE x %s S : p".format(toUtf.m_in))
    assert(chooseEx3 == "CHOOSE x : (p %s q)".format(toUtf.m_and))
    assert(chooseEx4 == "CHOOSE x %s (S %s T) : (p %s q)".format(toUtf.m_in, toUtf.m_times, toUtf.m_and))

    assertPrint(tla.label(tla.eql(a, b), "lab"), "lab∷ a = b")
    assertPrint(tla.label(tla.eql(a, b), "lab", "i", "j"), "lab(\"i\", \"j\")∷ a = b")

  }

  test("Test UTF8: TlaBoolOper") {
    val a = tla.name("a")
    val b = tla.name("b")
    val c = tla.name("c")
    val d = tla.name("d")
    val e = tla.name("e")
    val p = tla.name("p")
    val q = tla.name("q")

    val andEx1: String = toUtf(tla.and())
    val andEx2: String = toUtf(tla.and(a))
    val andEx3: String = toUtf(tla.and(a, b))
    val andEx4: String = toUtf(tla.and(a, tla.and(b, c)))
    val andEx5: String = toUtf(tla.and(a, tla.appOp(b)))

    assert(andEx1 == "")
    assert(andEx2 == "a")
    assert(andEx3 == "a %s b".format(toUtf.m_and))
    assert(andEx4 == "a %s (b %s c)".format(toUtf.m_and, toUtf.m_and))
    assert(andEx5 == "a %s b()".format(toUtf.m_and))

    val orEx1: String = toUtf(tla.or())
    val orEx2: String = toUtf(tla.or(a))
    val orEx3: String = toUtf(tla.or(a, b))
    val orEx4: String = toUtf(tla.or(a, tla.or(b, c)))
    val orEx5: String = toUtf(tla.or(a, tla.appOp(b)))

    assert(orEx1 == "")
    assert(orEx2 == "a")
    assert(orEx3 == "a %s b".format(toUtf.m_or))
    assert(orEx4 == "a %s (b %s c)".format(toUtf.m_or, toUtf.m_or))
    assert(orEx5 == "a %s b()".format(toUtf.m_or))

    val notEx1: String = toUtf(tla.not(a))
    val notEx2: String = toUtf(tla.not(tla.and(a, b)))

    assert(notEx1 == "%sa".format(toUtf.m_not))
    assert(notEx2 == "%s(a %s b)".format(toUtf.m_not, toUtf.m_and))

    val implEx1: String = toUtf(tla.impl(p, q))
    val implEx2: String = toUtf(tla.impl(tla.and(p, q), tla.or(a, b)))
    val implEx3: String = toUtf(tla.impl(tla.and(p), tla.and(q)))

    assert(implEx1 == "p %s q".format(toUtf.m_impl))
    assert(implEx2 == "(p %s q) %s (a %s b)".format(toUtf.m_and, toUtf.m_impl, toUtf.m_or))
    assert(implEx3 == "p %s q".format(toUtf.m_impl))

    val equivEx1: String = toUtf(tla.equiv(p, q))
    val equivEx2: String = toUtf(tla.equiv(tla.and(p, q), tla.or(a, b)))
    val equivEx3: String = toUtf(tla.equiv(tla.and(p), tla.and(q)))

    assert(equivEx1 == "p %s q".format(toUtf.m_equiv))
    assert(equivEx2 == "(p %s q) %s (a %s b)".format(toUtf.m_and, toUtf.m_equiv, toUtf.m_or))
    assert(equivEx3 == "p %s q".format(toUtf.m_equiv))

    val forallEx1: String = toUtf(tla.forall(a, b))
    val forallEx2: String = toUtf(tla.forall(a, tla.or(b, c)))
    val forallEx3: String = toUtf(tla.forall(a, b, c))
    val forallEx4: String =
      toUtf(tla.forall(a, tla.times(b, c), tla.and(d, e)))

    assert(forallEx1 == "%sa: b".format(toUtf.m_forall))
    assert(forallEx2 == "%sa: (b %s c)".format(toUtf.m_forall, toUtf.m_or))
    assert(forallEx3 == "%sa %s b: c".format(toUtf.m_forall, toUtf.m_in))
    assert(forallEx4 == "%sa %s (b %s c): (d %s e)".format(toUtf.m_forall, toUtf.m_in, toUtf.m_times, toUtf.m_and))

    val existsEx1: String = toUtf(tla.exists(a, b))
    val existsEx2: String = toUtf(tla.exists(a, tla.or(b, c)))
    val existsEx3: String = toUtf(tla.exists(a, b, c))
    val times = tla.times(b, c)
    val and = tla.and(d, e)
    val existsEx4: String = toUtf(tla.exists(a, times, and))

    assert(existsEx1 == "%sa: b".format(toUtf.m_exists))
    assert(existsEx2 == "%sa: (b %s c)".format(toUtf.m_exists, toUtf.m_or))
    assert(existsEx3 == "%sa %s b: c".format(toUtf.m_exists, toUtf.m_in))
    assert(existsEx4 == "%sa %s (b %s c): (d %s e)".format(toUtf.m_exists, toUtf.m_in, toUtf.m_times, toUtf.m_and))

  }

  test("Test UTF8: TlaArithOper") {
    val a = tla.name("a")
    val b = tla.name("b")
    val c = tla.name("c")

    assertPrint(tla.plus(a, b), "a + b")
    assertPrint(tla.minus(a, b), "a - b")
    assertPrint(tla.uminus(a), "-a")
    assertPrint(tla.uminus(tla.plus(a, b)), "-(a + b)")
    assertPrint(tla.mult(a, b), "a * b")
    assertPrint(tla.div(a, b), "a ÷ b")
    assertPrint(tla.mod(a, b), "a % b")
    assertPrint(tla.rDiv(a, b), "a / b")
    assertPrint(tla.exp(a, b), "a ^ b")
    assertPrint(tla.dotdot(a, b), "a .. b")
    assertPrint(tla.lt(a, b), "a < b")
    assertPrint(tla.gt(a, b), "a > b")
    assertPrint(tla.le(a, b), "a ≤ b")
    assertPrint(tla.ge(a, b), "a ≥ b")
    assertPrint(tla.plus(tla.mult(a, b), c), "(a * b) + c")
  }

  test("Test UTF8: TlaActionOper") {
    val p = tla.name("p")
    val q = tla.name("q")
    val x = tla.name("x")

    assertPrint(tla.prime(x), "x'")
    assertPrint(tla.prime(tla.plus(x, tla.int(1))), "(x + 1)'")
    assertPrint(tla.stutt(p, x), "[p]_x")
    assertPrint(tla.nostutt(p, x), "<p>_x")
    assertPrint(tla.enabled(p), "ENABLED p")
    assertPrint(tla.enabled(tla.and(p, q)), "ENABLED (p ∧ q)")
    assertPrint(tla.unchanged(x), "UNCHANGED x")
    assertPrint(tla.unchangedTup(tla.name("x"), tla.name("y")), "UNCHANGED (⟨x, y⟩)")
    assertPrint(tla.comp(p, q), "p ⋅ q")
    assertPrint(tla.comp(tla.and(p, q), tla.or(p, q)), "(p ∧ q) ⋅ (p ∨ q)")
  }

  test("Test UTF8: TlaControlOper") {
    val a = tla.name("a")
    val b = tla.name("b")
    val c = tla.name("c")
    val p = tla.name("p")
    val q = tla.name("q")

    assertPrint(tla.caseSplit(p, a), "CASE p → a")
    assertPrint(tla.caseSplit(p, a, q, b), "CASE p → a □ q → b")
    assertPrint(tla.caseOther(c, p, a), "CASE p → a □ OTHER → c")
    assertPrint(tla.caseOther(c, p, a, q, b), "CASE p → a □ q → b □ OTHER → c")
    assertPrint(tla.ite(p, a, b), "IF p THEN a ELSE b")
    assertPrint(tla.ite(tla.and(p, q), tla.plus(a, b), tla.minus(a, b)), "IF (p ∧ q) THEN (a + b) ELSE (a - b)")
  }

  test("Test UTF8: TlaTempOper") {
    val p = tla.name("p")
    val q = tla.name("q")
    val x = tla.name("x")

    assertPrint(tla.AA(x, p), "[∀]x . p")
    assertPrint(tla.EE(x, p), "[∃]x . p")
    assertPrint(tla.box(p), "□p")
    assertPrint(tla.box(tla.and(p, q)), "□(p ∧ q)")
    assertPrint(tla.diamond(p), "◇p")
    assertPrint(tla.diamond(tla.or(p, q)), "◇(p ∨ q)")
    assertPrint(tla.guarantees(p, q), "p ⇸ q")
    assertPrint(tla.leadsTo(p, q), "p ↝ q")
    assertPrint(tla.SF(x, p), "SF_x(p)")
    assertPrint(tla.WF(x, p), "WF_x(p)")
  }

  test("Test UTF8: TlaFiniteSetOper") {
    val S = tla.name("S")

    assertPrint(tla.card(S), "Cardinality(S)")
    assertPrint(tla.card(tla.enumSet(tla.int(1), tla.int(2))), "Cardinality({1, 2})")
    assertPrint(tla.isFin(S), "IsFiniteSet(S)")
    assertPrint(tla.isFin(tla.powSet(S)), "IsFiniteSet(SUBSET S)")
  }

  test("Test UTF8: TlaFunOper") {
    val S = tla.name("S")
    val T = tla.name("T")
    val a = tla.name("a")
    val b = tla.name("b")
    val f = tla.name("f")
    val i = tla.name("i")
    val j = tla.name("j")
    val v = tla.name("v")
    val x = tla.name("x")
    val y = tla.name("y")

    assertPrint(tla.appFun(f, i), "f[i]")
    assertPrint(tla.appFun(tla.appFun(f, i), j), "f[i][j]")
    assertPrint(tla.dom(f), "DOMAIN f")
    assertPrint(tla.dom(tla.appFun(f, i)), "DOMAIN f[i]")
    assertPrint(tla.enumFun(tla.str("foo"), a, tla.str("bar"), b), "[\"foo\" ↦ a, \"bar\" ↦ b]")
    assertPrint(tla.except(f, i, v), "[f EXCEPT ![i] = v]")
    assertPrint(tla.except(f, i, v, j, a), "[f EXCEPT ![i] = v, ![j] = a]")
    assertPrint(tla.funDef(tla.plus(x, y), x, S), "[x ∈ S ↦ x + y]")
    assertPrint(tla.funDef(tla.plus(x, y), x, S, y, T), "[x ∈ S, y ∈ T ↦ x + y]")
    assertPrint(tla.tuple(), "⟨⟩")
    assertPrint(tla.tuple(a), "⟨a⟩")
    assertPrint(tla.tuple(a, b), "⟨a, b⟩")
    assertPrint(tla.recFunRef(), "FUN_REC_REF")
    assertPrint(tla.recFunDef(tla.plus(x, tla.int(1)), x, S), "FUN_REC_CTOR(x + 1, x, S)")
  }

  test("Test UTF8: TlaSeqOper") {
    val S = tla.name("S")
    val T = tla.name("T")
    val a = tla.name("a")
    val b = tla.name("b")
    val s = tla.name("s")

    assertPrint(tla.append(s, a), "Append(s, a)")
    assertPrint(tla.append(tla.tuple(a), b), "Append(⟨a⟩, b)")
    assertPrint(tla.concat(S, T), "S ∘ T")
    assertPrint(tla.concat(tla.append(S, a), T), "(Append(S, a)) ∘ T")
    assertPrint(tla.head(s), "Head(s)")
    assertPrint(tla.tail(s), "Tail(s)")
    assertPrint(tla.len(s), "Len(s)")
    assertPrint(tla.subseq(s, tla.int(1), tla.int(2)), "Sequences!SubSeq(s, 1, 2)")
    assertPrint(OperEx(TlaSeqOper.subseq, tla.concat(S, T), tla.int(1), tla.len(S)),
        "Sequences!SubSeq(S ∘ T, 1, Len(S))")
  }

  test("Test UTF8: TlaSetOper") {
    val S = tla.name("S")
    val T = tla.name("T")
    val a = tla.name("a")
    val b = tla.name("b")
    val c = tla.name("c")
    val d = tla.name("d")
    val p = tla.name("p")
    val x = tla.name("x")
    val y = tla.name("y")

    val inEx1: String = toUtf(tla.in(a, b))
    val inEx2: String = toUtf(tla.and(tla.in(a, b), tla.in(c, d)))
    assert(inEx1 == "a %s b".format(toUtf.m_in))
    assert(inEx2 == "a %s b %s c %s d".format(toUtf.m_in, toUtf.m_and, toUtf.m_in))

    assertPrint(tla.emptySet(), "{}")
    assertPrint(tla.enumSet(a, b, c), "{a, b, c}")
    assertPrint(tla.in(tla.plus(a, b), S), "(a + b) ∈ S")
    assertPrint(tla.notin(a, S), "a ∉ S")
    assertPrint(tla.cap(S, T), "S ∩ T")
    assertPrint(tla.cup(S, T), "S ∪ T")
    assertPrint(tla.setminus(S, T), "S ∖ T")
    assertPrint(tla.subseteq(S, T), "S ⊆ T")
    assertPrint(tla.filter(x, S, p), "{x ∈ S: p}")
    assertPrint(tla.filter(x, tla.cup(S, T), tla.and(p, tla.in(x, S))), "{x ∈ (S ∪ T): (p ∧ x ∈ S)}")
    assertPrint(tla.funSet(S, T), "[S → T]")
    assertPrint(tla.map(tla.plus(x, y), x, S), "{x + y : x ∈ S}")
    assertPrint(tla.map(tla.plus(x, y), x, S, y, T), "{x + y : x ∈ S, y ∈ T}")
    assertPrint(tla.powSet(S), "SUBSET S")
    assertPrint(tla.recSet(tla.str("foo"), S, tla.str("bar"), T), "[\"foo\": S, \"bar\": T]")
    assertPrint(tla.seqSet(S), "Seq(S)")
    assertPrint(tla.times(S, T), "S × T")
    assertPrint(tla.times(S, T, tla.enumSet(a, b)), "S × T × {a, b}")
    assertPrint(tla.union(S), "UNION S")
  }

  test("Test UTF8: TlaAssumeDecl") {
    val x = tla.name("x")
    val namedAssume: String = toUtf(TlaAssumeDecl(Some("myAssume"), tla.eql(x, tla.bool(true))))
    assert(namedAssume == s"ASSUME myAssume ≜ x = TRUE")

    val unnamedAssume: String = toUtf(TlaAssumeDecl(None, tla.eql(x, tla.bool(true))))
    assert(unnamedAssume == s"ASSUME x = TRUE")
  }

  test("Test UTF8: declarations") {
    assertDeclPrint(TlaConstDecl("C"), "CONSTANT C")
    assertDeclPrint(TlaVarDecl("x"), "VARIABLE x")
    assertDeclPrint(TlaOperDecl("A", List(), tla.int(1)), "A ≜ 1")
    assertDeclPrint(TlaOperDecl("A", List(OperParam("x"), OperParam("y")), tla.plus(tla.name("x"), tla.name("y"))),
        "A(x, y) ≜ x + y")
    assertDeclPrint(TlaOperDecl("Apply", List(OperParam("F", 2), OperParam("x", 0)), tla.int(1)),
        "Apply(F(_, _), x) ≜ 1")

    val err = intercept[RuntimeException] {
      toUtf(TlaTheoremDecl("Thm", tla.bool(true)))
    }
    assert(err.getMessage.contains("Unexpected declaration"))
  }

  // regression
  test("Test UTF8: OperFormalParam") {
    val d = TlaOperDecl("Foo", List(OperParam("Bar", 1)), ValEx(TlaInt(1)))
    assert("Foo(Bar(_)) ≜ 1" == UTFPrinter(d))
  }

  // regression: LET-IN in the OTHER branch of CASE must be parenthesized.
  // Without parens, `CASE p -> a [] OTHER -> LET c == 1 IN c` re-parses any
  // following `/\ b` as inside the LET scope rather than outside the CASE.
  test("LET-IN in CASE OTHER branch is parenthesized") {
    val a = tla.name("a")
    val c = tla.name("c")
    val p = tla.name("p")
    val decl = TlaOperDecl("c", List(), ValEx(TlaInt(1)))
    val letInEx = tla.letIn(tla.appOp(c), decl)
    val caseEx = tla.caseOther(letInEx, p, a)
    assert(toUtf(caseEx).contains("OTHER → (LET c"))
  }

  test("Test UTF8: default operator printing") {
    val x = tla.name("x")
    val S = tla.name("S")

    assertPrint(OperEx(TlaFunOper.recFunRef), "FUN_REC_REF")
    assertPrint(OperEx(TlaFunOper.recFunDef, x, x, S), "FUN_REC_CTOR(x, x, S)")
    assertPrint(OperEx(ApalacheOper.gen, S), "Apalache!Gen(S)")
  }
}
