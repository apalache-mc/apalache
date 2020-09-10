package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.TlaReal
import at.forsyte.apalache.tla.lir.{UID, ValEx}
import at.forsyte.apalache.tla.typecheck.parser.DefaultType1Parser
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestTlaExTranslator extends FunSuite with BeforeAndAfterEach {
  var parser: Type1Parser = _
  var gen: TlaExTranslator = _

  override protected def beforeEach(): Unit = {
    parser = DefaultType1Parser
    gen = new TlaExTranslator()
  }

  private def mkAppByType(opexp: STCExpr, args: TlaType1*): STCApp = {
    STCApp(opexp,
      args.map(a => STCConst(a)(UID.unique)): _*)(UID.unique)
  }

  private def mkAppByName(opexp: STCExpr, args: String*): STCApp = {
    STCApp(opexp,
      args.map(a => STCName(a)(UID.unique)): _*)(UID.unique)
  }

  private def mkConstAppByType(opsig: TlaType1, args: TlaType1*): STCApp = {
    STCApp(STCConst(opsig)(UID.unique),
      args.map(a => STCConst(a)(UID.unique)): _*)(UID.unique)
  }

  private def mkConstAppByName(opsig: TlaType1, args: String*): STCApp = {
    STCApp(STCConst(opsig)(UID.unique),
      args.map(a => STCName(a)(UID.unique)): _*)(UID.unique)
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
    val parser = DefaultType1Parser
    val gen = new TlaExTranslator()

    // equality and inequality
    val a2ToBool = parser("(a, a) => Bool")
    val expected = mkConstAppByType(a2ToBool, parser("Int"), parser("Int"))
    assert(expected == gen(tla.eql(tla.int(1), tla.int(2))))
    assert(expected == gen(tla.neql(tla.int(1), tla.int(2))))
  }

  test("operator application") {
    // operator application should be just application
    val expected2 = STCApp(STCName("F")(UID.unique),
      STCConst(IntT1())(UID.unique),
      STCConst(BoolT1())(UID.unique))(UID.unique)

    assert(expected2 == gen(tla.appOp(tla.name("F"), tla.int(1), tla.bool(true))))
  }

  test("CHOOSE") {
      // the principal type of CHOOSE is (a => Bool) => a
    val chooseType = OperT1(Seq(OperT1(Seq(VarT1("a")), BoolT1())), VarT1("a"))
    // CHOOSE implicitly introduces a lambda abstraction: λ x ∈ S. P
    val chooseLambda = STCAbs(STCName("P")(UID.unique), ("x", STCName("S")(UID.unique)))(UID.unique)
    // the resulting expression is (((a => Bool) => a) (λ x ∈ S. P))
    val chooseExpected = STCApp(STCConst(chooseType)(UID.unique), chooseLambda)(UID.unique)
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
    val quantType = OperT1(Seq(OperT1(Seq(VarT1("a")), BoolT1())), BoolT1())
    // similar to CHOOSE, \E and \A implicitly introduce a lambda abstraction: λ x ∈ S. P
    val quantLambda = STCAbs(STCName("P")(UID.unique), ("x", STCName("S")(UID.unique)))(UID.unique)
    // the resulting expression is (((a => Bool) => Bool) (λ x ∈ S. P))
    val quantExpected = STCApp(STCConst(quantType)(UID.unique), quantLambda)(UID.unique)
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
    assert(expected == gen(tla.recSet(tla.str("x"), tla.name("S"), tla.str("y"), tla.name("T"))))
  }

  test("sequence set") {
    val setToSeq = parser("Set(a) => Seq(a)")
    val expected = mkConstAppByName(setToSeq, "S")
    assert(expected == gen(tla.seqSet(tla.name("S"))))
  }

  test("set membership") {
    val elemAndSetToBool = parser("(a, Set(a)) => Bool")
    val expected = mkConstAppByType(elemAndSetToBool, IntT1(), SetT1(IntT1()))
    assert(expected == gen(tla.in(tla.int(1), tla.intSet())))
    assert(expected == gen(tla.notin(tla.int(1), tla.intSet())))
  }

  test("\\union, \\intersect, \\setminus") {
    val binarySetOp = parser("(Set(a), Set(a)) => Set(a)")
    val expected = mkConstAppByType(binarySetOp, SetT1(IntT1()), SetT1(IntT1()))
    assert(expected == gen(tla.cup(tla.intSet(), tla.intSet())))
    assert(expected == gen(tla.cap(tla.intSet(), tla.intSet())))
    assert(expected == gen(tla.setminus(tla.intSet(), tla.intSet())))
  }

  test("\\subseteq, \\subset, \\supseteq, \\supset") {
    val elemAndSetToBool = parser("(Set(a), Set(a)) => Bool")
    val expected = mkConstAppByType(elemAndSetToBool, SetT1(IntT1()), SetT1(IntT1()))
    assert(expected == gen(tla.subset(tla.intSet(), tla.intSet())))
    assert(expected == gen(tla.subseteq(tla.intSet(), tla.intSet())))
    assert(expected == gen(tla.supseteq(tla.intSet(), tla.intSet())))
    assert(expected == gen(tla.supset(tla.intSet(), tla.intSet())))
  }

  test("SUBSET") {
    val setToPowerset = parser("Set(a) => Set(Set(a))")
    val expected = mkConstAppByType(setToPowerset, SetT1(IntT1()))
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
    val principal = OperT1(Seq(OperT1(Seq(VarT1("a")), BoolT1())), SetT1(VarT1("a")))
    // filter implicitly introduce a lambda abstraction: λ x ∈ S. P
    val lambda = STCAbs(STCName("P")(UID.unique), ("x", STCName("S")(UID.unique)))(UID.unique)
    // the resulting expression is (((a => Bool) => Set(a)) (λ x ∈ S. P))
    val expected = STCApp(STCConst(principal)(UID.unique), lambda)(UID.unique)
    assert(expected == gen(tla.filter(tla.name("x"), tla.name("S"), tla.name("P"))))
  }

  test("set map { x \\in S: e }") {
    // the principal type of is (b => a) => Set(a)
    val principal = OperT1(Seq(OperT1(Seq(VarT1("b")), VarT1("a"))), SetT1(VarT1("a")))
    // map implicitly introduces a lambda abstraction: λ x ∈ S. e
    val lambda = STCAbs(STCName("e")(UID.unique),
      ("x", STCName("S")(UID.unique)))(UID.unique)
    // the resulting expression is (b => a) => Set(a) (λ x ∈ S. e)
    val expected = STCApp(STCConst(principal)(UID.unique), lambda)(UID.unique)
    val map = tla.map(tla.name("e"),
      tla.name("x"), tla.name("S"))
    assert(expected == gen(map))
  }

  test("set map { x \\in S, y \\in T: e }") {
    // the principal type of is ((b, c) => a) => Set(a)
    val principal = OperT1(Seq(OperT1(Seq(VarT1("b"), VarT1("c")), VarT1("a"))), SetT1(VarT1("a")))
    // map implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. e
    val lambda = STCAbs(STCName("e")(UID.unique),
                        ("x", STCName("S")(UID.unique)), ("y", STCName("T")(UID.unique)))(UID.unique)
    // the resulting expression is ((b, c) => a) => Set(a) (λ x ∈ S, y ∈ T. e)
    val expected = STCApp(STCConst(principal)(UID.unique), lambda)(UID.unique)
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
    val tupleOrFun = STCConst(parser("(a, b) => <<a, b>>"), parser("(a, a) => Seq(a)")) (UID.unique)
    val expected = mkAppByType(tupleOrFun, IntT1(), IntT1())
    val tuple = tla.tuple(tla.int(1), tla.int(2))
    assert(expected == gen(tuple))
  }

  test("f[e]") {
    // when e is not a literal, f can be a function or a sequence
    val funOrSeq = STCConst(parser("((a -> b), a) => b"), parser("(Seq(a), Int) => a")) (UID.unique)
    val expected = mkAppByName(funOrSeq, "f", "e")
    val access = tla.appFun(tla.name("f"), tla.name("e"))
    assert(expected == gen(access))
  }

  test("f[2]") {
    // one of the three: a function, a sequence, or a tuple
    val funOrSeqOrTuple = STCConst(parser("((Int -> a), Int) => a"),
                            parser("(Seq(a), Int) => a"),
                            parser("({ 2: a }, Int) => a")) (UID.unique)
    val expected = STCApp(funOrSeqOrTuple, STCName("f") (UID.unique), STCConst(IntT1()) (UID.unique)) (UID.unique)
    val access = tla.appFun(tla.name("f"), tla.int(2))
    assert(expected == gen(access))
  }

  test("""f["foo"]""") {
    // either a function, or a record
    val funOrReq = STCConst(parser("((Str -> a), Str) => a"),
                            parser("([foo: a], Str) => a")) (UID.unique)
    val expected = STCApp(funOrReq, STCName("f") (UID.unique), STCConst(StrT1()) (UID.unique)) (UID.unique)
    val access = tla.appFun(tla.name("f"), tla.str("foo"))
    assert(expected == gen(access))
  }

  test("DOMAIN f") {
    // DOMAIN is applied to one of the four objects: a function, a sequence, a record, or a sparse tuple
    val types = STCConst(
      parser("(a -> b) => Set(a)"),
      parser("Seq(a) => Set(Int)"),
      parser("[] => Set(Str)"),
      parser("{} => Set(Int)")
    ) (UID.unique)
    val expected = mkAppByName(types, "f")
    val tuple = tla.dom(tla.name("f"))
    assert(expected == gen(tuple))
  }

  test("function definition [ x \\in S, y \\in T |-> e ]") {
    // the principal type is ((b, c) => a) => (<<b, c>> -> a)
    val principal = OperT1(Seq(OperT1(Seq(VarT1("b"), VarT1("c")), VarT1("a"))),
      FunT1(TupT1(VarT1("b"), VarT1("c")), VarT1("a")))
    // map implicitly introduces a lambda abstraction: λ x ∈ S, y ∈ T. e
    val lambda = STCAbs(STCName("e")(UID.unique),
      ("x", STCName("S")(UID.unique)), ("y", STCName("T")(UID.unique)))(UID.unique)
    // the resulting expression is (((b, c) => a) => (<<b, c>> -> a)) (λ x ∈ S, y ∈ T. e)
    val expected = STCApp(STCConst(principal)(UID.unique), lambda)(UID.unique)
    val fun = tla.funDef(tla.name("e"),
      tla.name("x"), tla.name("S"), tla.name("y"), tla.name("T"))
    assert(expected == gen(fun))
  }

  test("function update [ f EXCEPT ![e1] = e2 ]") {
    // a function or a sequence
    val types = STCConst(
      parser("((a -> b), a, b) => (a -> b)"),
      parser("(Seq(a), Int, a) => Seq(a)")) (UID.unique)

    val expected = mkAppByName(types, "f", "e1", "e2")
    val ex = tla.except(tla.name("f"), tla.name("e1"), tla.name("e2"))
    assert(expected == gen(ex))
  }

  test("function update [ f EXCEPT ![e1] = e2, ![e3] = e4 ]") {
    // a function or a sequence
    val types = STCConst(
      parser("((a -> b), a, b, a, b) => (a -> b)"),
      parser("(Seq(a), Int, a, Int, a) => Seq(a)")) (UID.unique)

    val expected = mkAppByName(types, "f", "e1", "e2", "e3", "e4")
    val ex = tla.except(tla.name("f"),
      tla.name("e1"), tla.name("e2"), tla.name("e3"), tla.name("e4"))
    assert(expected == gen(ex))
  }

  test("record update [ f EXCEPT !['foo'] = e2 ]") {
    // a function or a record
    val types = STCConst(
      parser("((a -> b), a, b) => (a -> b)"),
      parser("([foo: a], Str, a) => [foo: a]")) (UID.unique)

    val expected = STCApp(types, STCName("f") (UID.unique), STCConst(StrT1()) (UID.unique), STCName("e2") (UID.unique)) (UID.unique)
    val ex = tla.except(tla.name("f"), tla.str("foo"), tla.name("e2"))
    assert(expected == gen(ex))
  }

  test("tuple update [ f EXCEPT ![3] = e2 ]") {
    // a function or a record
    val types = STCConst(
      parser("((a -> b), a, b) => (a -> b)"),
      parser("(Seq(a), Int, a) => Seq(a)"),
      parser("({3: a}, Int, a) => {3: a}")) (UID.unique)

    val expected = STCApp(types, STCName("f") (UID.unique), STCConst(IntT1()) (UID.unique), STCName("e2") (UID.unique)) (UID.unique)
    val ex = tla.except(tla.name("f"), tla.int(3), tla.name("e2"))
    assert(expected == gen(ex))
  }

  test("tuple update [ f EXCEPT ![3] = e2 ], ![5] = e4") {
    // a function or a record
    val types = STCConst(
      parser("((a -> b), a, b, a, b) => (a -> b)"),
      parser("(Seq(a), Int, a, Int, a) => Seq(a)"),
      parser("({3: a, 5: b}, Int, a, Int, b) => {3: a, 5: b}")) (UID.unique)

    val expected = STCApp(types, STCName("f") (UID.unique),
      STCConst(IntT1()) (UID.unique), STCName("e2") (UID.unique),
      STCConst(IntT1()) (UID.unique), STCName("e4") (UID.unique)
    ) (UID.unique)
    val ex = tla.except(tla.name("f"),
      tla.int(3), tla.name("e2"), tla.int(5), tla.name("e4"))
    assert(expected == gen(ex))
  }

  test("recursive function definition f[x \\in Int] == x") {
    // the expected type is: ((a -> b) => (a -> b)) (λ $recFun ∈ Set(a -> b). λ x ∈ Int. x)
    val funType = FunT1(VarT1("a"), VarT1("b"))
    val principal = OperT1(Seq(funType), funType)
    // inner lambda
    val innerLambda = STCAbs(STCName("x")(UID.unique),
      ("x", STCConst(SetT1(IntT1())) (UID.unique))) (UID.unique)
    // outer lambda
    val outerLambda = STCAbs(innerLambda,
      (TlaFunOper.recFunRef.uniqueName, STCConst(SetT1(funType)) (UID.unique) )) (UID.unique)
    // the resulting expression is (a -> b) outerLambda
    val expected = STCApp(STCConst(principal)(UID.unique), outerLambda) (UID.unique)
    val fun = tla.recFunDef(tla.name("x"),
      tla.name("x"), tla.intSet())
    assert(expected == gen(fun))
  }

  test("recursive function call") {
    val expected = STCName(TlaFunOper.recFunRef.uniqueName) (UID.unique)
    val funRef = tla.recFunRef()
    assert(expected == gen(funRef))
  }

  test("IF e1 THEN e2 ELSE e3") {
    val iteType = STCConst(parser("(Bool, a, a) => a")) (UID.unique)
    val expected = mkAppByType(iteType, BoolT1(), IntT1(), IntT1())
    val ite = tla.ite(tla.bool(true), tla.int(1), tla.int(2))
    assert(expected == gen(ite))
  }

  test("CASE p1 -> e1 [] p2 -> e2") {
    val caseType = STCConst(parser("(Bool, a, Bool, a) => a")) (UID.unique)
    val expected = mkAppByType(caseType, BoolT1(), IntT1(), BoolT1(), IntT1())
    val caseEx = tla.caseSplit(tla.bool(true), tla.int(1), tla.bool(false), tla.int(2))
    assert(expected == gen(caseEx))
  }

  test("CASE p1 -> e1 [] p2 -> e2 OTHER e3") {
    val caseType = STCConst(parser("(Bool, a, Bool, a, a) => a")) (UID.unique)
    val expected = mkAppByType(caseType, BoolT1(), IntT1(), BoolT1(), IntT1(), IntT1())
    val caseEx = tla.caseOther(tla.bool(true), tla.int(1),
      tla.bool(false), tla.int(2), tla.int(3))
    assert(expected == gen(caseEx))
  }
}