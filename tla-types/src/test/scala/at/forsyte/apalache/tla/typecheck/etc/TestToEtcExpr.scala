package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.TlaReal
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
  var parser: Type1Parser = _
  var gen: ToEtcExpr = _

  override protected def beforeEach(): Unit = {
    parser = DefaultType1Parser
    gen = new ToEtcExpr()
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

    val int3ToInt = parser("(Int, Int, Int) => Int")
    val expected3 = mkConstAppByType(int3ToInt, parser("Int"), parser("Int"), parser("Int"))
    assert(expected3 == gen(tla.sum(tla.int(1), tla.int(2), tla.int(3))))
    assert(expected3 == gen(tla.prod(tla.int(1), tla.int(2), tla.int(3))))

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
    val expected = mkConstAppByType(a2ToBool, parser("Int"), parser("Int"))
    assert(expected == gen(tla.eql(tla.int(1), tla.int(2))))
    assert(expected == gen(tla.neql(tla.int(1), tla.int(2))))
  }

  test("operator application") {
    // operator application should be just application
    val expected2 = mkUniqAppByName("F", mkUniqConst(IntT1()), mkUniqConst(BoolT1()))

    assert(expected2 == gen(tla.appOp(tla.name("F"), tla.int(1), tla.bool(true))))
  }

  test("LET-IN simple") {
    // TODO: connect to type annotations
    // LET Foo(x) == x IN TRUE
    val foo = TlaOperDecl("Foo", List(SimpleFormalParam("x")), tla.name("x"))
    // becomes: let Foo = λ x ∈ Set(a). x in Bool
    val fooType = mkUniqAbs(mkUniqName("x"), ("x", mkUniqConst(SetT1(VarT1("a")))))
    val ex = LetInEx(tla.bool(true), foo)
    val expected = mkUniqLet("Foo", fooType, mkUniqConst(BoolT1()))
    assert(expected == gen(ex))
  }

  test("LET-IN higher order") {
    // TODO: connect to type annotations
    // LET Foo(Bar(_)) == 1 IN TRUE
    val foo = TlaOperDecl("Foo", List(OperFormalParam("Bar", 1)), tla.int(1))
    // becomes: let Foo = λ Bar ∈ Set(a => b). Int in Bool
    val fooType = mkUniqAbs(mkUniqConst(IntT1()), ("Bar", mkUniqConst(parser("Set(a => b)"))))
    val ex = LetInEx(tla.bool(true), foo)
    val expected = mkUniqLet("Foo", fooType, mkUniqConst(BoolT1()))
    assert(expected == gen(ex))
  }

  test("CHOOSE") {
    // the principal type of CHOOSE is (a => Bool) => a
    val chooseType = parser("(a => Bool) => a")
    // CHOOSE implicitly introduces a lambda abstraction: λ x ∈ S. P
    val chooseLambda = mkUniqAbs(mkUniqName("P"), ("x", mkUniqName("S")))
    // the resulting expression is (((a => Bool) => a) (λ x ∈ S. P))
    val chooseExpected = mkUniqApp(Seq(chooseType), chooseLambda)
    assert(chooseExpected == gen(tla.choose(tla.name("x"), tla.name("S"), tla.name("P"))))
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
    // the principal type of \A and \E is (a => Bool) => Bool
    val quantType = parser("(a => Bool) => Bool")
    // similar to CHOOSE, \E and \A implicitly introduce a lambda abstraction: λ x ∈ S. P
    val quantLambda = mkUniqAbs(mkUniqName("P"), ("x", mkUniqName("S")))
    // the resulting expression is (((a => Bool) => Bool) (λ x ∈ S. P))
    val quantExpected = mkUniqApp(Seq(quantType), quantLambda)
    assert(quantExpected == gen(tla.exists(tla.name("x"), tla.name("S"), tla.name("P"))))
    assert(quantExpected == gen(tla.forall(tla.name("x"), tla.name("S"), tla.name("P"))))
  }

  test("set enumerator") {
    val ternary = parser("(a, a, a) => Set(a)")
    val expected = mkConstAppByType(ternary, parser("Int"), parser("Int"), parser("Int"))
    assert(expected == gen(tla.enumSet(tla.int(1), tla.int(2), tla.int(3))))
  }

  test("[S -> T]") {
    val setsToFunSet = parser("(Set(a), Set(b)) => Set(a -> b)")
    val expected = mkConstAppByType(setsToFunSet, parser("Set(Int)"), parser("Set(Int)"))
    assert(expected == gen(tla.funSet(tla.intSet(), tla.intSet())))
  }

  test("record set constructor") {
    val funOperType = parser("(Set(a), Set(b)) => Set([x: a, y: b])")
    val expected = mkConstAppByName(funOperType, "S", "T")
    assert(expected == gen(tla.recSet(tla.str("x"), tla.name("S"),
      tla.str("y"), tla.name("T"))))
  }

  test("sequence set") {
    val setToSeq = parser("Set(a) => Seq(a)")
    val expected = mkConstAppByName(setToSeq, "S")
    assert(expected == gen(tla.seqSet(tla.name("S"))))
  }

  test("set membership") {
    val elemAndSetToBool = parser("(a, Set(a)) => Bool")
    val expected = mkConstAppByType(elemAndSetToBool, parser("Int"), parser("Set(Int)"))
    assert(expected == gen(tla.in(tla.int(1), tla.intSet())))
    assert(expected == gen(tla.notin(tla.int(1), tla.intSet())))
  }

  test("\\union, \\intersect, \\setminus") {
    val binarySetOp = parser("(Set(a), Set(a)) => Set(a)")
    val expected = mkConstAppByType(binarySetOp, parser("Set(Int)"), parser("Set(Int)"))
    assert(expected == gen(tla.cup(tla.intSet(), tla.intSet())))
    assert(expected == gen(tla.cap(tla.intSet(), tla.intSet())))
    assert(expected == gen(tla.setminus(tla.intSet(), tla.intSet())))
  }

  test("\\subseteq, \\subset, \\supseteq, \\supset") {
    val elemAndSetToBool = parser("(Set(a), Set(a)) => Bool")
    val expected = mkConstAppByType(elemAndSetToBool, parser("Set(Int)"), parser("Set(Int)"))
    assert(expected == gen(tla.subset(tla.intSet(), tla.intSet())))
    assert(expected == gen(tla.subseteq(tla.intSet(), tla.intSet())))
    assert(expected == gen(tla.supseteq(tla.intSet(), tla.intSet())))
    assert(expected == gen(tla.supset(tla.intSet(), tla.intSet())))
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
    val lambda = mkUniqAbs(mkUniqName("P"), ("x", mkUniqName("S")))
    // the resulting expression is (((a => Bool) => Set(a)) (λ x ∈ S. P))
    val expected = mkUniqApp(Seq(principal), lambda)
    assert(expected == gen(tla.filter(tla.name("x"), tla.name("S"), tla.name("P"))))
  }

  test("set map { x \\in S: e }") {
    // the principal type of is (b => a) => Set(a)
    val principal = parser("(b => a) => Set(a)")
    // map implicitly introduces a lambda abstraction: λ x ∈ S. e
    val lambda = mkUniqAbs(mkUniqName("e"), ("x", mkUniqName("S")))
    // the resulting expression is ((b => a) => Set(a)) (λ x ∈ S. e)
    val expected = mkUniqApp(Seq(principal), lambda)
    val map = tla.map(tla.name("e"),
      tla.name("x"), tla.name("S"))
    assert(expected == gen(map))
  }

  test("set map { x \\in S, y \\in T: e }") {
    // the principal type of is ((b, c) => a) => Set(a)
    val principal = parser("((b, c) => a) => Set(a)")
    // map implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. e
    val lambda = mkUniqAbs(mkUniqName("e"),
      ("x", mkUniqName("S")), ("y", mkUniqName("T")))
    // the resulting expression is ((b, c) => a) => Set(a) (λ x ∈ S, y ∈ T. e)
    val expected = mkUniqApp(Seq(principal), lambda)
    val map = tla.map(tla.name("e"),
      tla.name("x"), tla.name("S"), tla.name("y"), tla.name("T"))
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
      Seq(parser("((Int -> a), Int) => a"),
        parser("(Seq(a), Int) => a"),
        parser("({ 2: a }, Int) => a"))
    val expected = mkUniqApp(funOrSeqOrTuple, mkUniqName("f"), mkUniqConst(IntT1()))
    val access = tla.appFun(tla.name("f"), tla.int(2))
    assert(expected == gen(access))
  }

  test("""f["foo"]""") {
    // either a function, or a record
    val funOrReq = Seq(parser("((Str -> a), Str) => a"),
                       parser("([foo: a], Str) => a"))
    val expected = mkUniqApp(funOrReq, mkUniqName("f"), mkUniqConst(StrT1()))
    val access = tla.appFun(tla.name("f"), tla.str("foo"))
    assert(expected == gen(access))
  }

  test("DOMAIN f") {
    // DOMAIN is applied to one of the four objects: a function, a sequence, a record, or a sparse tuple
    val types = Seq(
      parser("(a -> b) => Set(a)"),
      parser("Seq(a) => Set(Int)"),
      parser("[] => Set(Str)"),
      parser("{} => Set(Int)"))

    val expected = mkAppByName(types, "f")
    val tuple = tla.dom(tla.name("f"))
    assert(expected == gen(tuple))
  }

  test("function definition [ x \\in S, y \\in T |-> e ]") {
    // the principal type is ((b, c) => a) => (<<b, c>> -> a)
    val principal =  parser("((b, c) => a) => (<<b, c>> -> a)")
    // map implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. e
    val lambda = mkUniqAbs(mkUniqName("e"),
      ("x", mkUniqName("S")), ("y", mkUniqName("T")))
    // the resulting expression is (((b, c) => a) => (<<b, c>> -> a)) (λ x ∈ S, y ∈ T. e)
    val expected = mkUniqApp(Seq(principal), lambda)
    val fun = tla.funDef(tla.name("e"),
      tla.name("x"), tla.name("S"), tla.name("y"), tla.name("T"))
    assert(expected == gen(fun))
  }

  test("function update [ f EXCEPT ![e1] = e2 ]") {
    // a function or a sequence
    val types = Seq(
      parser("((a -> b), a, b) => (a -> b)"),
      parser("(Seq(a), Int, a) => Seq(a)"))

    val expected = mkAppByName(types, "f", "e1", "e2")
    val ex = tla.except(tla.name("f"), tla.name("e1"), tla.name("e2"))
    assert(expected == gen(ex))
  }

  test("function update [ f EXCEPT ![e1] = e2, ![e3] = e4 ]") {
    // a function or a sequence
    val types = Seq(
      parser("((a -> b), a, b, a, b) => (a -> b)"),
      parser("(Seq(a), Int, a, Int, a) => Seq(a)"))

    val expected = mkAppByName(types, "f", "e1", "e2", "e3", "e4")
    val ex = tla.except(tla.name("f"),
      tla.name("e1"), tla.name("e2"), tla.name("e3"), tla.name("e4"))
    assert(expected == gen(ex))
  }

  test("record update [ f EXCEPT !['foo'] = e2 ]") {
    // a function or a record
    val types = Seq(
      parser("((a -> b), a, b) => (a -> b)"),
      parser("([foo: a], Str, a) => [foo: a]"))

    val expected = mkUniqApp(types, mkUniqName("f"), mkUniqConst(StrT1()), mkUniqName("e2"))
    val ex = tla.except(tla.name("f"), tla.str("foo"), tla.name("e2"))
    assert(expected == gen(ex))
  }

  test("tuple update [ f EXCEPT ![3] = e2 ]") {
    // a function or a record
    val types = Seq(
      parser("((a -> b), a, b) => (a -> b)"),
      parser("(Seq(a), Int, a) => Seq(a)"),
      parser("({3: a}, Int, a) => {3: a}"))

    val expected = mkUniqApp(types, mkUniqName("f"), mkUniqConst(IntT1()), mkUniqName("e2"))
    val ex = tla.except(tla.name("f"), tla.int(3), tla.name("e2"))
    assert(expected == gen(ex))
  }

  test("tuple update [ f EXCEPT ![3] = e2 ], ![5] = e4") {
    // a function or a record
    val types = Seq(
      parser("((a -> b), a, b, a, b) => (a -> b)"),
      parser("(Seq(a), Int, a, Int, a) => Seq(a)"),
      parser("({3: a, 5: b}, Int, a, Int, b) => {3: a, 5: b}"))

    val expected = mkUniqApp(types, mkUniqName("f"),
      mkUniqConst(IntT1()), mkUniqName("e2"),
      mkUniqConst(IntT1()), mkUniqName("e4"))
    val ex = tla.except(tla.name("f"),
      tla.int(3), tla.name("e2"), tla.int(5), tla.name("e4"))
    assert(expected == gen(ex))
  }

  test("recursive function definition f[x \\in Int] == x") {
    // the expected expression is:
    //   ((a -> b) => a => b) => a -> b) (λ $recFun ∈ Set(c -> d)) (λ x ∈ Set(Int). x)
    val principal = parser("((a -> b) => (a => b)) => (a -> b)")
    // inner lambda
    val innerLambda = mkUniqAbs(mkUniqName("x"),
      ("x", mkUniqConst(SetT1(IntT1()))))
    // outer lambda
    val outerLambda = mkUniqAbs(innerLambda,
      (TlaFunOper.recFunRef.uniqueName, mkUniqConst(parser("Set(c -> d)"))))
    // the resulting expression is ((a -> b), (a => b)) => (a -> b) outerLambda
    val expected = mkUniqApp(Seq(principal), outerLambda)
    val fun = tla.recFunDef(tla.name("x"),
      tla.name("x"), tla.intSet())
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
    val caseType = parser("(Bool, a, Bool, a, a) => a")
    val expected = mkAppByType(Seq(caseType), BoolT1(), IntT1(), BoolT1(), IntT1(), IntT1())
    val caseEx = tla.caseOther(tla.bool(true), tla.int(1),
      tla.bool(false), tla.int(2), tla.int(3))
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

  test("UNCHANGED") {
    val typ = parser("a => Bool")
    val expected = mkAppByName(Seq(typ), "x")
    val ex = tla.unchanged(tla.name("x"))
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
    val typ = parser("(a, Bool) => Bool")
    val expected = mkAppByName(Seq(typ), "x", "A")
    assert(expected == gen(tla.WF(tla.name("x"), tla.name("A"))))
    assert(expected == gen(tla.SF(tla.name("x"), tla.name("A"))))
  }

  test("\\EE x: A and \\AA x: A") {
    val typ = parser("(a, Bool) => Bool")
    val expected = mkAppByName(Seq(typ), "x", "A")
    assert(expected == gen(tla.AA(tla.name("x"), tla.name("A"))))
    assert(expected == gen(tla.EE(tla.name("x"), tla.name("A"))))
  }
}