package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.io.annotations.StandardAnnotations
import at.forsyte.apalache.io.annotations.store.{AnnotationStore, createAnnotationStore}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaFunOper, TlcOper}
import at.forsyte.apalache.tla.lir.values.TlaReal
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.typecheck.parser.DefaultType1Parser
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

/**
 * Unit tests for translating TLA+ expressions to EtcExpr.
 *
 * @author Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestToEtcExpr extends FunSuite with BeforeAndAfterEach with EtcBuilder {
  private var parser: Type1Parser = _
  private var annotationStore: AnnotationStore = _
  private var gen: ToEtcExpr = _

  override protected def beforeEach(): Unit = {
    parser = DefaultType1Parser
    annotationStore = createAnnotationStore()
    // a new instance of the translator, as it gives unique names to the variables
    gen = new ToEtcExpr(annotationStore, new TypeVarPool())
  }

  private def mkAppByType(operTypes: Seq[TlaType1], args: TlaType1*): EtcApp = {
    mkUniqApp(operTypes, args.map(a => mkUniqConst(a)): _*)
  }

  private def mkAppByName(operTypes: Seq[TlaType1], args: String*): EtcApp = {
    mkUniqApp(operTypes, args.map(mkUniqName): _*)
  }

  private def mkConstAppByType(opsig: TlaType1, args: TlaType1*): EtcApp = {
    mkUniqApp(Seq(opsig), args.map(a => mkUniqConst(a)): _*)
  }

  private def mkConstAppByName(opsig: TlaType1, args: String*): EtcApp = {
    mkUniqApp(Seq(opsig), args.map(mkUniqName): _*)
  }

  // produce an expression that projects a set of pairs on the set of its first (or second) components
  private def mkProjection(fst: String, snd: String, projFirst: Boolean, set: String): EtcExpr = {
    val axis = if (projFirst) fst else snd
    val tuple = TupT1(VarT1(fst), VarT1(snd))
    // Projection: depending on axis, either ((<<a, b>>, Set(<<a, b>>)) => Set(a)) or ((<<a, b>>, Set(<<a, b>>)) => Set(b))
    // We add the tuple <<a, b>> for technical reasons, in order to recover the type of the variable tuple in TypeRewriter.
    val oper = OperT1(Seq(tuple, SetT1(tuple)), SetT1(VarT1(axis)))
    mkUniqApp(Seq(oper), mkUniqConst(tuple), mkUniqName(set))
  }

  test("integer arithmetic") {
    // integers
    val intToInt = parser("Int => Int")
    val expected = mkConstAppByType(intToInt, parser("Int"))
    assert(expected == gen(tla.uminus(tla.int(1))))

    val int2ToInt = parser("(Int, Int) => Int")
    val expected2 = mkConstAppByType(int2ToInt, parser("Int"), parser("Int"))
    assert(expected2 == gen(tla.plus(tla.int(1), tla.int(2))))
    assert(expected2 == gen(tla.minus(tla.int(1), tla.int(2))))
    assert(expected2 == gen(tla.mult(tla.int(1), tla.int(2))))
    assert(expected2 == gen(tla.div(tla.int(1), tla.int(2))))
    assert(expected2 == gen(tla.mod(tla.int(1), tla.int(2))))
    assert(expected2 == gen(tla.exp(tla.int(1), tla.int(2))))

    val int2ToSetInt = parser("(Int, Int) => Set(Int)")
    val expected2Set = mkConstAppByType(int2ToSetInt, parser("Int"), parser("Int"))
    assert(expected2Set == gen(tla.dotdot(tla.int(1), tla.int(3))))

    val int2ToBool = parser("(Int, Int) => Bool")
    val expected2Bool = mkConstAppByType(int2ToBool, parser("Int"), parser("Int"))
    assert(expected2Bool == gen(tla.lt(tla.int(1), tla.int(2))))
    assert(expected2Bool == gen(tla.gt(tla.int(1), tla.int(2))))
    assert(expected2Bool == gen(tla.le(tla.int(1), tla.int(2))))
    assert(expected2Bool == gen(tla.ge(tla.int(1), tla.int(2))))
  }

  test("real arithmetic") {
    // reals
    val real2ToInt = parser("(Real, Real) => Real")
    val expectedReal = mkConstAppByType(real2ToInt, parser("Real"), parser("Real"))
    assert(expectedReal == gen(tla.rDiv(ValEx(TlaReal()), ValEx(TlaReal()))))
  }

  test("equality and inequality") {
    // equality and inequality
    val a2ToBool = parser("(a, a) => Bool")

    def mkExpected(tt: TlaType1) = mkConstAppByType(tt, parser("Int"), parser("Int"))

    assert(mkExpected(parser("(a, a) => Bool")) == gen(tla.eql(tla.int(1), tla.int(2))))
    assert(mkExpected(parser("(b, b) => Bool")) == gen(tla.neql(tla.int(1), tla.int(2))))
  }

  test("operator application") {
    // operator application should be just application
    val fName = mkUniqName("F")
    val expected2 = mkUniqAppByName(fName, mkUniqConst(IntT1()), mkUniqConst(BoolT1()))

    assert(expected2 == gen(tla.appOp(tla.name("F"), tla.int(1), tla.bool(true))))
  }

  test("LET-IN simple") {
    // LET Foo(x) == x IN TRUE
    val foo = TlaOperDecl("Foo", List(SimpleFormalParam("x")), tla.name("x"))
    // becomes: let Foo = λ x ∈ Set(a). x in Bool
    val fooType = mkUniqAbs(mkUniqName("x"), (mkUniqName("x"), mkUniqConst(SetT1(VarT1("a")))))
    val ex = LetInEx(tla.bool(true), foo)
    val let = mkUniqLet("Foo", fooType, mkUniqConst(BoolT1()))
    // we wrap the let-definition with an application of an identity operator, to recover the type of LetInEx later
    val expected = mkUniqApp(Seq(parser("b => b")), let)
    assert(expected == gen(ex))
  }

  test("LET-IN with a java-like type annotation") {
    // LET
    //   \* @type: Int => Int;
    //   Foo(x) == x IN TRUE
    val foo = TlaOperDecl("Foo", List(SimpleFormalParam("x")), tla.name("x"))
    annotationStore += foo.ID -> List(StandardAnnotations.mkType("Int => Int"))
    // becomes:
    // Foo: (Int => Int) in
    // let Foo = λ x ∈ Set(a). x in Bool
    val fooType = mkUniqAbs(mkUniqName("x"), (mkUniqName("x"), mkUniqConst(SetT1(VarT1("a")))))
    val tlaLetIn = LetInEx(tla.bool(true), foo)
    val etcLet = mkUniqLet("Foo", fooType, mkUniqConst(BoolT1()))
    val etcAnnotation = mkUniqTypeDecl("Foo", parser("Int => Int"), etcLet)
    // we wrap the annotated let-definition with an application of an identity operator, to recover the type of LetInEx later
    val expected = mkUniqApp(Seq(parser("b => b")), etcAnnotation)
    assert(expected == gen(tlaLetIn))
  }

  test("LET-IN higher order") {
    // LET Foo(Bar(_)) == 1 IN TRUE
    val foo = TlaOperDecl("Foo", List(OperFormalParam("Bar", 1)), tla.int(1))
    // becomes: let Foo = λ Bar ∈ Set(a => b). Int in Bool
    val fooType = mkUniqAbs(mkUniqConst(IntT1()), (mkUniqName("Bar"), mkUniqConst(parser("Set(a => b)"))))
    val ex = LetInEx(tla.bool(true), foo)
    val let = mkUniqLet("Foo", fooType, mkUniqConst(BoolT1()))
    // we wrap the let-definition with an application of an identity operator, to recover the type of LetInEx later
    val expected = mkUniqApp(Seq(parser("c => c")), let)
    assert(expected == gen(ex))
  }

  test("CHOOSE") {
    // The bounded form: CHOOSE x |in S: P.
    // the principal type of CHOOSE is (a => Bool) => a
    val chooseType = parser("(a => Bool) => a")
    // CHOOSE implicitly introduces a lambda abstraction: λ x ∈ S. P
    val chooseLambda = mkUniqAbs(mkUniqName("P"), (mkUniqName("x"), mkUniqName("S")))
    // the resulting expression is (((a => Bool) => a) (λ x ∈ S. P))
    val chooseExpected = mkUniqApp(Seq(chooseType), chooseLambda)
    assert(chooseExpected == gen(tla.choose(tla.name("x"), tla.name("S"), tla.name("P"))))
  }

  test("unbounded CHOOSE") {
    // The unbounded form: CHOOSE x: P. The only hope to figure out the type is to use the type of the predicate P.
    // the principal type of CHOOSE is (a => Bool) => a
    val chooseType = parser("(a => Bool) => a")
    // CHOOSE implicitly introduces a lambda abstraction: λ x ∈ S. P
    val chooseLambda = mkUniqAbs(mkUniqName("P"), (mkUniqName("x"), mkUniqConst(SetT1(VarT1("b")))))
    // the resulting expression is (((a => Bool) => a) (λ x ∈ Set(a). P))
    val chooseExpected = mkUniqApp(Seq(chooseType), chooseLambda)
    assert(chooseExpected == gen(tla.choose(tla.name("x"), tla.name("P"))))
  }

  test("binary Boolean connectives") {
    val bool2ToBool = parser("(Bool, Bool) => Bool")
    val expected = mkConstAppByType(bool2ToBool, parser("Bool"), parser("Bool"))
    assert(expected == gen(tla.and(tla.bool(true), tla.bool(false))))
    assert(expected == gen(tla.or(tla.bool(true), tla.bool(false))))
    assert(expected == gen(tla.impl(tla.bool(true), tla.bool(false))))
    assert(expected == gen(tla.equiv(tla.bool(true), tla.bool(false))))
  }

  test("unary Boolean connectives") {
    val boolToBool = parser("(Bool) => Bool")
    val expected = mkConstAppByType(boolToBool, parser("Bool"))
    assert(expected == gen(tla.not(tla.bool(true))))
  }

  test("quantifiers: \\E and \\A") {
    // similar to CHOOSE, \E and \A implicitly introduce a lambda abstraction: λ x ∈ S. P
    val quantLambda = mkUniqAbs(mkUniqName("P"), (mkUniqName("x"), mkUniqName("S")))

    // the resulting expression is (((a => Bool) => Bool) (λ x ∈ S. P))
    def mkExpected(tt: TlaType1) = mkUniqApp(Seq(tt), quantLambda)
    // the principal type of \A and \E is (a => Bool) => Bool
    assert(mkExpected(parser("(a => Bool) => Bool")) == gen(tla.exists(tla.name("x"), tla.name("S"), tla.name("P"))))
    assert(mkExpected(parser("(b => Bool) => Bool")) == gen(tla.forall(tla.name("x"), tla.name("S"), tla.name("P"))))
  }

  test("existential over tuples: \\E <<x, y>> \\in S: P") {
    // we have to project a set of tuples onto two sets of their components
    val proj_x = mkProjection("a", "b", projFirst = true, "S")
    val proj_y = mkProjection("c", "d", projFirst = false, "S")
    val quantLambda = mkUniqAbs(mkUniqName("P"), (mkUniqName("x"), proj_x), (mkUniqName("y"), proj_y))

    // the resulting expression is ((((e, f) => Bool) => Bool) (λ x ∈ proj_x. λ y ∈ proj_y. P))
    def mkExpected(tt: TlaType1) = mkUniqApp(Seq(tt), quantLambda)

    val exists = tla.exists(tla.tuple(tla.name("x"), tla.name("y")), tla.name("S"), tla.name("P"))
    assert(mkExpected(parser("((e, f) => Bool) => Bool")) == gen(exists))
  }

  test("universal over tuples: \\A <<x, y>> \\in S: P") {
    // we have to project a set of tuples onto two sets of their components
    val proj_x = mkProjection("a", "b", projFirst = true, "S")
    val proj_y = mkProjection("c", "d", projFirst = false, "S")
    val quantLambda = mkUniqAbs(mkUniqName("P"), (mkUniqName("x"), proj_x), (mkUniqName("y"), proj_y))

    // the resulting expression is ((((e, f) => Bool) => Bool) (λ x ∈ proj_x. λ y ∈ proj_y. P))
    def mkExpected(tt: TlaType1) = mkUniqApp(Seq(tt), quantLambda)

    val exists = tla.forall(tla.tuple(tla.name("x"), tla.name("y")), tla.name("S"), tla.name("P"))
    assert(mkExpected(parser("((e, f) => Bool) => Bool")) == gen(exists))
  }

  test("set enumerator") {
    val ternary = parser("(a, a, a) => Set(a)")
    val expected = mkConstAppByType(ternary, parser("Int"), parser("Int"), parser("Int"))
    assert(expected == gen(tla.enumSet(tla.int(1), tla.int(2), tla.int(3))))
  }

  test("{}") {
    val expected = mkUniqConst(parser("Set(a)"))
    val result = gen(tla.enumSet())
    assert(expected == result)
  }

  test("<<>>") {
    val expected = mkUniqConst(parser("Seq(a)"))
    val result = gen(tla.tuple())
    assert(expected == result)
  }

  test("[S -> T]") {
    val setsToFunSet = parser("(Set(a), Set(b)) => Set(a -> b)")
    val expected = mkConstAppByType(setsToFunSet, parser("Set(Int)"), parser("Set(Int)"))
    assert(expected == gen(tla.funSet(tla.intSet(), tla.intSet())))
  }

  test("record set constructor") {
    val funOperType = parser("(Set(a), Set(b)) => Set([x: a, y: b])")
    val expected = mkConstAppByName(funOperType, "S", "T")
    assert(expected == gen(tla.recSet(tla.str("x"), tla.name("S"), tla.str("y"), tla.name("T"))))
  }

  test("invalid field string in record set construction") {
    val invalid = "invalidName"
    val exn = intercept[IllegalArgumentException](
        gen(tla.recSet(tla.name(invalid), tla.str("x")))
    )
    assert(exn.getMessage.contains(invalid))
  }

  test("sequence set") {
    val setToSeq = parser("Set(a) => Set(Seq(a))")
    val expected = mkConstAppByName(setToSeq, "S")
    assert(expected == gen(tla.seqSet(tla.name("S"))))
  }

  test("set membership") {
    def mkExpected(tt: TlaType1) = mkConstAppByType(tt, parser("Int"), parser("Set(Int)"))

    assert(mkExpected(parser("(a, Set(a)) => Bool")) == gen(tla.in(tla.int(1), tla.intSet())))
    assert(mkExpected(parser("(b, Set(b)) => Bool")) == gen(tla.notin(tla.int(1), tla.intSet())))
  }

  test("\\union, \\intersect, \\setminus") {
    val binarySetOp = parser("(Set(a), Set(a)) => Set(a)")

    def mkExpected(tt: TlaType1) = mkConstAppByType(tt, parser("Set(Int)"), parser("Set(Int)"))

    assert(mkExpected(parser("(Set(a), Set(a)) => Set(a)")) == gen(tla.cup(tla.intSet(), tla.intSet())))
    assert(mkExpected(parser("(Set(b), Set(b)) => Set(b)")) == gen(tla.cap(tla.intSet(), tla.intSet())))
    assert(mkExpected(parser("(Set(c), Set(c)) => Set(c)")) == gen(tla.setminus(tla.intSet(), tla.intSet())))
  }

  test("\\subseteq, \\subset, \\supseteq, \\supset") {
    def mkExpected(tt: TlaType1) = mkConstAppByType(tt, parser("Set(Int)"), parser("Set(Int)"))

    assert(mkExpected(parser("(Set(a), Set(a)) => Bool")) == gen(tla.subset(tla.intSet(), tla.intSet())))
    assert(mkExpected(parser("(Set(b), Set(b)) => Bool")) == gen(tla.subseteq(tla.intSet(), tla.intSet())))
    assert(mkExpected(parser("(Set(c), Set(c)) => Bool")) == gen(tla.supseteq(tla.intSet(), tla.intSet())))
    assert(mkExpected(parser("(Set(d), Set(d)) => Bool")) == gen(tla.supset(tla.intSet(), tla.intSet())))
  }

  test("SUBSET") {
    val setToPowerset = parser("Set(a) => Set(Set(a))")
    val expected = mkConstAppByType(setToPowerset, parser("Set(Int)"))
    assert(expected == gen(tla.powSet(tla.intSet())))
  }

  test("UNION") {
    val powersetToSet = parser("Set(Set(a)) => Set(a)")
    val expected = mkConstAppByName(powersetToSet, "S")
    assert(expected == gen(tla.union(tla.name("S"))))
  }

  test("\\X") {
    val cartesian = parser("(Set(a), Set(b)) => Set(<<a, b>>)")
    val expected = mkConstAppByName(cartesian, "S", "T")
    assert(expected == gen(tla.times(tla.name("S"), tla.name("T"))))
  }

  test("set filter { x \\in S: P }") {
    // the principal type of is (a => Bool) => Set(a)
    val principal = parser("(a => Bool) => Set(a)")
    // filter implicitly introduce a lambda abstraction: λ x ∈ S. P
    val lambda = mkUniqAbs(mkUniqName("P"), (mkUniqName("x"), mkUniqName("S")))
    // the resulting expression is (((a => Bool) => Set(a)) (λ x ∈ S. P))
    val expected = mkUniqApp(Seq(principal), lambda)
    assert(expected == gen(tla.filter(tla.name("x"), tla.name("S"), tla.name("P"))))
  }

  test("set filter { <<x, y>> \\in S: P }") {
    // the principal type of is ((e, f) => Bool) => Set(<<e, f>>)
    val principal = parser("((e, f) => Bool) => Set(<<e, f>>)")
    // filter implicitly introduce a lambda abstraction: λ x ∈ (...), y ∈ (...). P
    // the binding <<x, y>> \in S gives us two lambda abstractions

    val proj_x = mkProjection("a", "b", projFirst = true, "S")
    val proj_y = mkProjection("c", "d", projFirst = false, "S")
    val lambda = mkUniqAbs(mkUniqName("P"), (mkUniqName("x"), proj_x), (mkUniqName("y"), proj_y))
    // the resulting expression is ((((e, f) => Bool) => Set(<<e, f>>)) (λ x ∈ proj_x, y ∈ proj_y. P))
    val expected = mkUniqApp(Seq(principal), lambda)
    assert(expected == gen(tla.filter(tla.tuple(tla.name("x"), tla.name("y")), tla.name("S"), tla.name("P"))))
  }

  test("set map { x \\in S: e }") {
    // the principal type of is (b => a) => Set(a)
    val principal = parser("(b => a) => Set(a)")
    // map implicitly introduces a lambda abstraction: λ x ∈ S. e
    val lambda = mkUniqAbs(mkUniqName("e"), (mkUniqName("x"), mkUniqName("S")))
    // the resulting expression is ((b => a) => Set(a)) (λ x ∈ S. e)
    val expected = mkUniqApp(Seq(principal), lambda)
    val map = tla.map(tla.name("e"), tla.name("x"), tla.name("S"))
    assert(expected == gen(map))
  }

  // translating the advanced syntax in set comprehensions
  test("set map { <<x, y>> \\in S: e }") {
    // given an operator from (f, g) to e, map it to the set of e: ((f, g) => e) => Set(e)
    val principal = parser("((f, g) => e) => Set(e)")
    // the binding <<x, y>> \in S gives us two lambda abstractions
    val proj_x = mkProjection("a", "b", projFirst = true, "S")
    val proj_y = mkProjection("c", "d", projFirst = false, "S")
    val lambda = mkUniqAbs(mkUniqName("e"), (mkUniqName("x"), proj_x), (mkUniqName("y"), proj_y))

    // the resulting expression is (((f, g) => e) => Set(e)) (λ x ∈ (...), y ∈ (...). e)
    val expected = mkUniqApp(Seq(principal), lambda)
    // { <<x, y>> \in S: e }
    val map = tla.map(tla.name("e"), tla.tuple(tla.name("x"), tla.name("y")), tla.name("S"))
    assert(expected == gen(map))
  }

  test("set map { x \\in S, y \\in T: e }") {
    // the principal type of is ((b, c) => a) => Set(a)
    val principal = parser("((b, c) => a) => Set(a)")
    // map implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. e
    val lambda = mkUniqAbs(mkUniqName("e"), (mkUniqName("x"), mkUniqName("S")), (mkUniqName("y"), mkUniqName("T")))
    // the resulting expression is ((b, c) => a) => Set(a) (λ x ∈ S, y ∈ T. e)
    val expected = mkUniqApp(Seq(principal), lambda)
    val map = tla.map(tla.name("e"), tla.name("x"), tla.name("S"), tla.name("y"), tla.name("T"))
    assert(expected == gen(map))
  }

  test("[f1 |-> TRUE, f2 |-> 1]") {
    // here we have simply the record type
    val funOperType = parser("(a, b) => [f1: a, f2: b]")
    val expected = mkConstAppByType(funOperType, BoolT1(), IntT1())
    val rec = tla.enumFun(tla.str("f1"), tla.bool(true), tla.str("f2"), tla.int(1))
    assert(expected == gen(rec))
  }

  test("<<1, 2>>") {
    val tupleOrFun = Seq(parser("(a, b) => <<a, b>>"), parser("(a, a) => Seq(a)"))
    val expected = mkAppByType(tupleOrFun, IntT1(), IntT1())
    val tuple = tla.tuple(tla.int(1), tla.int(2))
    assert(expected == gen(tuple))
  }

  test("f[e]") {
    // when e is not a literal, f can be a function or a sequence
    val funOrSeq = Seq(parser("((a -> b), a) => b"), parser("(Seq(a), Int) => a"))
    val expected = mkAppByName(funOrSeq, "f", "e")
    val access = tla.appFun(tla.name("f"), tla.name("e"))
    assert(expected == gen(access))
  }

  test("f[2]") {
    // one of the three: a function, a sequence, or a tuple
    val funOrSeqOrTuple =
      Seq(parser("((Int -> a), Int) => a"), parser("(Seq(a), Int) => a"), parser("({ 2: a }, Int) => a"))
    val expected = mkUniqApp(funOrSeqOrTuple, mkUniqName("f"), mkUniqConst(IntT1()))
    val access = tla.appFun(tla.name("f"), tla.int(2))
    assert(expected == gen(access))
  }

  test("""f["foo"]""") {
    // either a function, or a record
    val funOrReq = Seq(parser("((Str -> a), Str) => a"), parser("([foo: a], Str) => a"))
    val expected = mkUniqApp(funOrReq, mkUniqName("f"), mkUniqConst(StrT1()))
    val access = tla.appFun(tla.name("f"), tla.str("foo"))
    assert(expected == gen(access))
  }

  test("DOMAIN f") {
    // DOMAIN is applied to one of the four objects: a function, a sequence, a record, or a sparse tuple
    val types = Seq(parser("(a -> b) => Set(a)"), parser("Seq(a) => Set(Int)"), parser("[] => Set(Str)"),
        parser("{} => Set(Int)"))

    val expected = mkAppByName(types, "f")
    val tuple = tla.dom(tla.name("f"))
    assert(expected == gen(tuple))
  }

  test("one-argument function definition [ x \\in S |-> e ]") {
    // the principal type is (b => a) => (b -> a)
    val principal = parser("(b => a) => (b -> a)")
    // map implicitly introduces a lambda abstraction: λ x ∈ S. e
    val lambda = mkUniqAbs(mkUniqName("e"), (mkUniqName("x"), mkUniqName("S")))
    // the resulting expression is ((b => a) => (b -> a)) (λ x ∈ S. e)
    val expected = mkUniqApp(Seq(principal), lambda)
    val fun = tla.funDef(tla.name("e"), tla.name("x"), tla.name("S"))
    assert(expected == gen(fun))
  }

  test("function definition [ x \\in S, y \\in T |-> ex ]") {
    // the principal type is ((b, c) => a) => (<<b, c>> -> a)
    val principal = parser("((b, c) => a) => (<<b, c>> -> a)")
    // map implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. ex
    val lambda = mkUniqAbs(mkUniqName("ex"), (mkUniqName("x"), mkUniqName("S")), (mkUniqName("y"), mkUniqName("T")))
    // the resulting expression is (((b, c) => a) => (<<b, c>> -> a)) (λ x ∈ S, y ∈ T. e)
    val expected = mkUniqApp(Seq(principal), lambda)
    val fun = tla.funDef(tla.name("ex"), tla.name("x"), tla.name("S"), tla.name("y"), tla.name("T"))
    assert(expected == gen(fun))
  }

  test("function definition [ <<x, y>> \\in S |-> ex ]") {
    // the principal type is ((f, g) => e) => (<<f, g>> -> e)
    val principal = parser("((f, g) => e) => (<<f, g>> -> e)")
    // the binding <<x, y>> \in S gives us a lambda of two arguments
    val proj_x = mkProjection("a", "b", projFirst = true, "S")
    val proj_y = mkProjection("c", "d", projFirst = false, "S")
    val lambda = mkUniqAbs(mkUniqName("ex"), (mkUniqName("x"), proj_x), (mkUniqName("y"), proj_y))
    // the resulting expression is (((f, g) => e) => (<<f, g>> -> e)) (λ x ∈ (...), y ∈ (...). ex)
    val expected = mkUniqApp(Seq(principal), lambda)
    val fun = tla.funDef(tla.name("ex"), tla.tuple(tla.name("x"), tla.name("y")), tla.name("S"))
    assert(expected == gen(fun))
  }

  test("function update [ f EXCEPT ![e1] = e2 ]") {
    // a function or a sequence
    val types = Seq(parser("((a -> b), a, b) => (a -> b)"), parser("(Seq(a), Int, a) => Seq(a)"))

    val expected = mkAppByName(types, "f", "e1", "e2")
    val ex = tla.except(tla.name("f"), tla.tuple(tla.name("e1")), tla.name("e2"))
    assert(expected == gen(ex))
  }

  test("function update [ f EXCEPT ![e1] = e2, ![e3] = e4 ]") {
    // a function or a sequence
    val types = Seq(parser("((a -> b), a, b, a, b) => (a -> b)"), parser("(Seq(a), Int, a, Int, a) => Seq(a)"))

    val expected = mkAppByName(types, "f", "e1", "e2", "e3", "e4")
    val ex =
      tla.except(tla.name("f"), tla.tuple(tla.name("e1")), tla.name("e2"), tla.tuple(tla.name("e3")), tla.name("e4"))
    assert(expected == gen(ex))
  }

  test("record update [ f EXCEPT !['foo'] = e2 ]") {
    // a function or a record
    val types = Seq(parser("((a -> b), a, b) => (a -> b)"), parser("([foo: c], Str, c) => [foo: c]"))

    val expected = mkUniqApp(types, mkUniqName("f"), mkUniqConst(StrT1()), mkUniqName("e2"))
    val ex = tla.except(tla.name("f"), tla.tuple(tla.str("foo")), tla.name("e2"))
    assert(expected == gen(ex))
  }

  test("tuple update [ f EXCEPT ![3] = e2 ]") {
    // a function or a record
    val types = Seq(parser("((a -> b), a, b) => (a -> b)"), parser("(Seq(a), Int, a) => Seq(a)"),
        parser("({3: c}, Int, c) => {3: c}"))

    val expected = mkUniqApp(types, mkUniqName("f"), mkUniqConst(IntT1()), mkUniqName("e2"))
    val ex = tla.except(tla.name("f"), tla.tuple(tla.int(3)), tla.name("e2"))
    assert(expected == gen(ex))
  }

  test("tuple update [ f EXCEPT ![3] = e2 ], ![5] = e4") {
    // a function or a record
    val types = Seq(parser("((a -> b), a, b, a, b) => (a -> b)"), parser("(Seq(a), Int, a, Int, a) => Seq(a)"),
        parser("({3: c, 5: d}, Int, c, Int, d) => {3: c, 5: d}"))

    val expected =
      mkUniqApp(types, mkUniqName("f"), mkUniqConst(IntT1()), mkUniqName("e2"), mkUniqConst(IntT1()), mkUniqName("e4"))
    val ex = tla.except(tla.name("f"), tla.tuple(tla.int(3)), tla.name("e2"), tla.tuple(tla.int(5)), tla.name("e4"))
    assert(expected == gen(ex))
  }

  test("recursive function definition f[x \\in Int] == x") {
    // the expected expression is:
    //   (((b -> a) => (b => a)) => (b -> a)) (λ $recFun ∈ Set(d -> c). (λ x ∈ Set(Int). x))
    val principal = parser("((b -> a) => (b => a)) => (b -> a)")
    // inner lambda
    val innerLambda = mkUniqAbs(mkUniqName("x"), (mkUniqName("x"), mkUniqConst(SetT1(IntT1()))))
    // outer lambda
    val outerLambda =
      mkUniqAbs(innerLambda, (mkUniqName(TlaFunOper.recFunRef.uniqueName), mkUniqConst(parser("Set(d -> c)"))))
    // the resulting expression is (((b -> a), (b => a)) => (b -> a)) outerLambda
    val expected = mkUniqApp(Seq(principal), outerLambda)
    val fun = tla.recFunDef(tla.name("x"), tla.name("x"), tla.intSet())
    assert(expected == gen(fun))
  }

  test("binary recursive function definition f[x \\in Int, y \\in Bool] == x") {
    // the expected expression is:
    //   (((<<b, c>> -> a) => ((b, c) => a)) => (<<b, c>> -> a))
    //      (λ $recFun ∈ Set(<<e, f>> -> d). (λ x ∈ Set(Int), y ∈ Set(Bool). x))
    val principal = parser("((<<b, c>> -> a) => ((b, c) => a)) => (<<b, c>> -> a)")
    // inner lambda
    val innerLambda =
      mkUniqAbs(mkUniqName("x"), (mkUniqName("x"), mkUniqConst(SetT1(IntT1()))),
          (mkUniqName("y"), mkUniqConst(SetT1(BoolT1()))))
    // outer lambda
    val outerLambda =
      mkUniqAbs(innerLambda, (mkUniqName(TlaFunOper.recFunRef.uniqueName), mkUniqConst(parser("Set(<<e, f>> -> d)"))))
    // the resulting expression is (principal outerLambda)
    val expected = mkUniqApp(Seq(principal), outerLambda)
    val fun = tla.recFunDef(tla.name("x"), tla.name("x"), tla.intSet(), tla.name("y"), tla.booleanSet())
    assert(expected == gen(fun))
  }

  test("recursive function definition with tuples f[<<x, y>> \\in S] == x") {
    // the expected expression is:
    //   (((<<f, g>> -> e) => ((f, g) => e)) => (<<f, g>> -> e))
    //      (λ $recFun ∈ Set(<<i, j>> -> h). (λ x ∈ Proj_x, y ∈ Proj_y. x))
    // where Proj_x and Proj_y are projections of S on the first and second coordinates, respectively.
    val principal = parser("((<<f, g>> -> e) => ((f, g) => e)) => (<<f, g>> -> e)")
    // inner lambda
    // the binding <<x, y>> \in S gives us a lambda of two arguments
    val proj_x = mkProjection("a", "b", projFirst = true, "S")
    val proj_y = mkProjection("c", "d", projFirst = false, "S")
    val innerLambda = mkUniqAbs(mkUniqName("x"), (mkUniqName("x"), proj_x), (mkUniqName("y"), proj_y))
    // outer lambda
    val outerLambda =
      mkUniqAbs(innerLambda, (mkUniqName(TlaFunOper.recFunRef.uniqueName), mkUniqConst(parser("Set(<<i, j>> -> h)"))))
    // the resulting expression is (principal outerLambda)
    val expected = mkUniqApp(Seq(principal), outerLambda)
    val fun = tla.recFunDef(tla.name("x"), tla.tuple(tla.name("x"), tla.name("y")), tla.name("S"))
    assert(expected == gen(fun))
  }

  test("recursive function call") {
    val expected = mkUniqName(TlaFunOper.recFunRef.uniqueName)
    val funRef = tla.recFunRef()
    assert(expected == gen(funRef))
  }

  test("IF e1 THEN e2 ELSE e3") {
    val iteType = parser("(Bool, a, a) => a")
    val expected = mkAppByType(Seq(iteType), BoolT1(), IntT1(), IntT1())
    val ite = tla.ite(tla.bool(true), tla.int(1), tla.int(2))
    assert(expected == gen(ite))
  }

  test("CASE p1 -> e1 [] p2 -> e2") {
    val caseType = parser("(Bool, a, Bool, a) => a")
    val expected = mkAppByType(Seq(caseType), BoolT1(), IntT1(), BoolT1(), IntT1())
    val caseEx = tla.caseSplit(tla.bool(true), tla.int(1), tla.bool(false), tla.int(2))
    assert(expected == gen(caseEx))
  }

  test("CASE p1 -> e1 [] p2 -> e2 OTHER e3") {
    // CASE..OTHER has the default argument first
    val caseType = parser("(a, Bool, a, Bool, a) => a")
    val expected = mkAppByType(Seq(caseType), IntT1(), BoolT1(), IntT1(), BoolT1(), IntT1())
    val caseEx = tla.caseOther(tla.int(3), tla.bool(true), tla.int(1), tla.bool(false), tla.int(2))
    assert(expected == gen(caseEx))
  }

  test("IsFinite(S)") {
    val finType = parser("(Set(a) => Bool)")
    val expected = mkAppByName(Seq(finType), "S")
    val ex = tla.isFin(tla.name("S"))
    assert(expected == gen(ex))
  }

  test("Cardinality(S)") {
    val finType = parser("(Set(a) => Int)")
    val expected = mkAppByName(Seq(finType), "S")
    val ex = tla.card(tla.name("S"))
    assert(expected == gen(ex))
  }

  test("Prime") {
    val typ = parser("(a => a)")
    val expected = mkAppByName(Seq(typ), "x")
    val ex = tla.prime(tla.name("x"))
    assert(expected == gen(ex))
  }

  test("stutter") {
    val typ = parser("(Bool, a) => Bool")
    val expected = mkAppByName(Seq(typ), "A", "x")
    val ex = tla.stutt(tla.name("A"), tla.name("x"))
    assert(expected == gen(ex))
  }

  test("no stutter") {
    val typ = parser("(Bool, a) => Bool")
    val expected = mkAppByName(Seq(typ), "A", "x")
    val ex = tla.nostutt(tla.name("A"), tla.name("x"))
    assert(expected == gen(ex))
  }

  test("ENABLED") {
    val typ = parser("Bool => Bool")
    val expected = mkAppByName(Seq(typ), "A")
    val ex = tla.enabled(tla.name("A"))
    assert(expected == gen(ex))
  }

  test("UNCHANGED x") {
    val typ = parser("a => Bool")
    val expected = mkAppByName(Seq(typ), "x")
    val ex = tla.unchanged(tla.name("x"))
    assert(expected == gen(ex))
  }

  test("UNCHANGED <<x>>") {
    val ex = tla.unchanged(tla.tuple(tla.name("x")))
    val tupleType = mkAppByName(Seq(parser("a => <<a>>")), "x")
    val expected = mkUniqApp(Seq(parser("<<a>> => Bool")), tupleType)
    assert(expected == gen(ex))
  }

  test("UNCHANGED <<x, y>>") {
    val ex = tla.unchanged(tla.tuple(tla.name("x"), tla.name("y")))
    val tupleType = mkAppByName(Seq(parser("(a, b) => <<a, b>>")), "x", "y")
    val expected = mkUniqApp(Seq(parser("<<a, b>> => Bool")), tupleType)
    assert(expected == gen(ex))
  }

  test("composition") {
    val typ = parser("(Bool, Bool) => Bool")
    val expected = mkAppByName(Seq(typ), "A", "B")
    val ex = tla.comp(tla.name("A"), tla.name("B"))
    assert(expected == gen(ex))
  }

  test("Head(seq)") {
    val typ = parser("Seq(a) => a")
    val expected = mkAppByName(Seq(typ), "seq")
    val ex = tla.head(tla.name("seq"))
    assert(expected == gen(ex))
  }

  test("Tail(seq)") {
    val typ = parser("Seq(a) => Seq(a)")
    val expected = mkAppByName(Seq(typ), "seq")
    val ex = tla.tail(tla.name("seq"))
    assert(expected == gen(ex))
  }

  test("Append(seq, x)") {
    val typ = parser("(Seq(a), a) => Seq(a)")
    val expected = mkAppByName(Seq(typ), "seq", "x")
    val ex = tla.append(tla.name("seq"), tla.name("x"))
    assert(expected == gen(ex))
  }

  test("s \\o t") {
    val typ = parser("(Seq(a), Seq(a)) => Seq(a)")
    val expected = mkAppByName(Seq(typ), "s", "t")
    val ex = tla.concat(tla.name("s"), tla.name("t"))
    assert(expected == gen(ex))
  }

  test("Len(s)") {
    val typ = parser("Seq(a) => Int")
    val expected = mkAppByName(Seq(typ), "s")
    val ex = tla.len(tla.name("s"))
    assert(expected == gen(ex))
  }

  test("SubSeq(s, 2, 3)") {
    val typ = parser("(Seq(a), Int, Int) => Seq(a)")
    val expected = mkAppByName(Seq(typ), "s", "i", "j")
    val ex = tla.subseq(tla.name("s"), tla.name("i"), tla.name("j"))
    assert(expected == gen(ex))
  }

  test("SelectSeq(s, A)") {
    val typ = parser("(Seq(a), (a => Bool)) => Seq(a)")
    val expected = mkAppByName(Seq(typ), "s", "A")
    val ex = tla.selectseq(tla.name("s"), tla.name("A"))
    assert(expected == gen(ex))
  }

  test("Labels") {
    val typ = parser("(Str, Str, Str, a) => a")
    val expected =
      mkUniqApp(Seq(typ), mkUniqConst(StrT1()), mkUniqConst(StrT1()), mkUniqConst(StrT1()), mkUniqName("x"))
    val ex = tla.label(tla.name("x"), "lab", "a", "b")
    assert(expected == gen(ex))
  }

  test("Apalache!FunAsSeq(fun, len)") {
    val typ = parser("(Int -> a, Int) => Seq(a)")
    val expected = mkAppByName(Seq(typ), "fun", "len")
    val ex = OperEx(ApalacheOper.funAsSeq, tla.name("fun"), tla.name("len"))
    assert(expected == gen(ex))
  }

  test("Apalache!:=") {
    val typ = parser("(a, a) => Bool")
    val expected = mkAppByName(Seq(typ), "x", "y")
    val ex = OperEx(ApalacheOper.assign, tla.name("x"), tla.name("y"))
    assert(expected == gen(ex))
  }

  test("Apalache!Skolem") {
    val typ = parser("Bool => Bool")
    val expected = mkAppByName(Seq(typ), "P")
    val ex = OperEx(ApalacheOper.skolem, tla.name("P"))
    assert(expected == gen(ex))
  }

  test("Apalache!Expand") {
    val typ = parser("a => a")
    val expected = mkAppByName(Seq(typ), "S")
    val ex = OperEx(ApalacheOper.expand, tla.name("S"))
    assert(expected == gen(ex))
  }

  test("Apalache!ConstCard") {
    val typ = parser("Bool => Bool")
    val expected = mkAppByName(Seq(typ), "P")
    val ex = OperEx(ApalacheOper.constCard, tla.name("P"))
    assert(expected == gen(ex))
  }

  test("Apalache!Distinct") {
    val typ = parser("(a, a) => Bool")
    val expected = mkAppByName(Seq(typ), "x", "y")
    val ex = OperEx(ApalacheOper.distinct, tla.name("x"), tla.name("y"))
    assert(expected == gen(ex))
  }

  test("unary temporal operators") {
    val unary = parser("Bool => Bool")
    val expectedUnary = mkAppByName(Seq(unary), "A")
    assert(expectedUnary == gen(tla.box(tla.name("A"))))
    assert(expectedUnary == gen(tla.diamond(tla.name("A"))))
  }

  test("binary temporal operators") {
    val binary = parser("(Bool, Bool) => Bool")
    val expectedBinary = mkAppByName(Seq(binary), "A", "B")
    assert(expectedBinary == gen(tla.leadsTo(tla.name("A"), tla.name("B"))))
    assert(expectedBinary == gen(tla.guarantees(tla.name("A"), tla.name("B"))))
  }

  test("WF_x(A) and SF_x(A)") {
    def mkExpected(tt: TlaType1) = mkAppByName(Seq(tt), "x", "A")

    assert(mkExpected(parser("(a, Bool) => Bool")) == gen(tla.WF(tla.name("x"), tla.name("A"))))
    assert(mkExpected(parser("(b, Bool) => Bool")) == gen(tla.SF(tla.name("x"), tla.name("A"))))
  }

  test("old annotations: e <: tp") {
    val oldTypeAnnotation = tla.enumSet(tla.intSet())
    // we explicitly use OperEx here, as we have removed Builder.withType
    val input = OperEx(ApalacheOper.withType, tla.name("e"), oldTypeAnnotation)(Untyped())
    assertThrows[OutdatedAnnotationsError](gen(input))
  }

  test("TLC!Print") {
    val typ = parser("(Str, a) => Str")
    val ex = OperEx(TlcOper.print, tla.name("text"), tla.name("x"))
    val expected = mkAppByName(Seq(typ), "text", "x")
    assert(expected == gen(ex))
  }

  test("TLC!PrintT") {
    val typ = parser("Str => Bool")
    val ex = OperEx(TlcOper.printT, tla.str("hello "))
    val expected = mkAppByType(Seq(typ), StrT1())
    assert(expected == gen(ex))
  }

  test("TLC!Assert") {
    val typ = parser("(a, Str) => Bool")
    val ex = OperEx(TlcOper.assert, tla.name("x"), tla.name("y"))
    val expected = mkAppByName(Seq(typ), "x", "y")
    assert(expected == gen(ex))
  }

  test("TLC!JavaTime") {
    val typ = parser("() => Int")
    val ex = OperEx(TlcOper.javaTime)
    val expected = mkAppByName(Seq(typ))
    assert(expected == gen(ex))
  }

  test("TLC!TLCGet") {
    val typ = parser("Int => a")
    val ex = OperEx(TlcOper.tlcGet, tla.int(3))
    val expected = mkAppByType(Seq(typ), IntT1())
    assert(expected == gen(ex))
  }

  test("TLC!TLCSet") {
    val typ = parser("(Int, a) => Bool")
    val ex = OperEx(TlcOper.tlcSet, tla.name("x"), tla.name("y"))
    val expected = mkAppByName(Seq(typ), "x", "y")
    assert(expected == gen(ex))
  }

  test("TLC!:>") {
    val typ = parser("(a, b) => (a -> b)")
    val ex = OperEx(TlcOper.colonGreater, tla.name("x"), tla.name("y"))
    val expected = mkAppByName(Seq(typ), "x", "y")
    assert(expected == gen(ex))
  }

  test("TLC!@@") {
    val typ = parser("(a -> b, a -> b) => (a -> b)")
    val ex = OperEx(TlcOper.atat, tla.name("f"), tla.name("g"))
    val expected = mkAppByName(Seq(typ), "f", "g")
    assert(expected == gen(ex))
  }

  test("TLC!Permutations") {
    val typ = parser("Set(a) => Set(a -> a)")
    val ex = OperEx(TlcOper.permutations, tla.name("S"))
    val expected = mkAppByName(Seq(typ), "S")
    assert(expected == gen(ex))
  }

  test("TLC!SortSeq") {
    val typ = parser("(Seq(a), ((a, a) => Bool)) => Seq(a)")
    val ex = OperEx(TlcOper.sortSeq, tla.name("seq"), tla.name("op"))
    val expected = mkAppByName(Seq(typ), "seq", "op")
    assert(expected == gen(ex))
  }

  test("TLC!RandomElement") {
    val typ = parser("Set(a) => a")
    val ex = OperEx(TlcOper.randomElement, tla.name("S"))
    val expected = mkAppByName(Seq(typ), "S")
    assert(expected == gen(ex))
  }

  test("TLC!Any") {
    val typ = parser("() => a")
    val ex = OperEx(TlcOper.any)
    val expected = mkAppByName(Seq(typ))
    assert(expected == gen(ex))
  }

  test("TLC!ToString") {
    val typ = parser("a => Str")
    val ex = OperEx(TlcOper.tlcToString, tla.name("x"))
    val expected = mkAppByName(Seq(typ), "x")
    assert(expected == gen(ex))
  }

  test("TLC!TLCEval") {
    val typ = parser("a => a")
    val ex = OperEx(TlcOper.tlcEval, tla.name("x"))
    val expected = mkAppByName(Seq(typ), "x")
    assert(expected == gen(ex))
  }
}
