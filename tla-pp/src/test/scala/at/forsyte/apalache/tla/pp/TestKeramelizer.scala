package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs.BuilderExAsTyped
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations.PredResultOk
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard.{KeraLanguagePred, KeramelizerInputLanguagePred}
import org.junit.runner.RunWith
import org.scalacheck.Prop.{forAll, propBoolean}
import org.scalatest.AppendedClues.convertToClueful
import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestKeramelizer extends AnyFunSuite with Checkers with BeforeAndAfterEach with Matchers {
  private var keramelizer = new Keramelizer(new UniqueNameGenerator(), TrackerWithListeners())

  override def beforeEach(): Unit = {
    keramelizer = new Keramelizer(new UniqueNameGenerator(), TrackerWithListeners())
  }

  test("""X \intersect Y""") {
    val types = Map("e" -> IntT1, "s" -> SetT1(IntT1), "b" -> BoolT1)
    val input = tla
      .cap(tla.name("X") ? "s", tla.name("Y") ? "s")
      .typed(types, "s")
    val output = keramelizer.apply(input)
    val expected =
      tla
        .filter(tla.name("t_1") ? "e", tla.name("X") ? "s", tla.in(tla.name("t_1") ? "e", tla.name("Y") ? "s") ? "b")
        .typed(types, "s")
    assert(expected == output)
  }

  test("intersect under another expression") {
    val types = Map("s" -> SetT1(IntT1), "e" -> IntT1, "b" -> BoolT1)
    val input =
      tla
        .cup(tla.name("Z") ? "s", tla.cap(tla.name("X") ? "s", tla.name("Y") ? "s") ? "s")
        .typed(types, "s")
    val output = keramelizer.apply(input)
    val transformed =
      tla.filter(tla.name("t_1") ? "e", tla.name("X") ? "s", tla.in(tla.name("t_1") ? "e", tla.name("Y") ? "s") ? "b")
    val expected =
      tla
        .cup(tla.name("Z") ? "s", transformed ? "s")
        .typed(types, "s")
    assert(expected == output)
  }

  test("""X \ Y""") {
    val types = Map("s" -> SetT1(IntT1), "e" -> IntT1, "b" -> BoolT1)
    val input = tla
      .setminus(tla.name("X") ? "s", tla.name("Y") ? "s")
      .typed(types, "s")
    val output = keramelizer.apply(input)
    val expected =
      tla
        .filter(tla.name("t_1") ? "e", tla.name("X") ? "s",
            tla.not(tla.in(tla.name("t_1") ? "e", tla.name("Y") ? "s") ? "b") ? "b")
        .typed(types, "s")
    assert(expected == output)
  }

  test("""x \notin Y ~~> ~(x \in Y)""") {
    val types = Map("s" -> SetT1(IntT1), "e" -> IntT1, "b" -> BoolT1)
    val input = tla
      .notin(tla.name("x") ? "e", tla.name("Y") ? "s")
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected: TlaEx =
      tla
        .not(tla.in(tla.name("x") ? "e", tla.name("Y") ? "s") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""a <=> b ~~> a = b""") {
    val types = Map("i" -> SetT1(IntT1), "b" -> BoolT1)
    val input = tla
      .equiv(tla.name("a") ? "i", tla.name("b") ? "i")
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected =
      tla
        .eql(tla.name("a") ? "i", tla.name("b") ? "i")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""a => b ~~> ~a \/ b""") {
    val types = Map("b" -> BoolT1)
    val input = tla
      .impl(tla.name("a") ? "b", tla.name("b") ? "b")
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected =
      tla
        .or(tla.not(tla.name("a") ? "b") ? "b", tla.name("b") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""a /= b ~~> ~(a = b)""") {
    val types = Map("b" -> BoolT1)
    val input = tla
      .neql(tla.name("a") ? "b", tla.name("b") ? "b")
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected =
      tla
        .not(tla.eql(tla.name("a") ? "b", tla.name("b") ? "b") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""[a: A, b: B] ~~> {[a |-> t_1, b |-> t_2]: t_1 \in A, t_2 \in B}""") {
    val types = Map(
        "a" -> BoolT1,
        "b" -> StrT1,
        "A" -> SetT1(BoolT1),
        "B" -> SetT1(StrT1),
        "s" -> StrT1,
        "r" -> RecT1("a" -> BoolT1, "b" -> StrT1),
        "R" -> SetT1(RecT1("a" -> BoolT1, "b" -> StrT1)),
    )
    val input =
      tla
        .recSet(tla.name("a") ? "s", tla.name("A") ? "A", tla.name("b") ? "s", tla.name("B") ? "B")
        .typed(types, "R")
    val output = keramelizer.apply(input)
    val rec = tla.enumFun(tla.name("a") ? "s", tla.name("t_1") ? "a", tla.name("b") ? "s", tla.name("t_2") ? "b")
    val expected =
      tla
        .map(
            rec ? "r",
            tla.name("t_1") ? "a",
            tla.name("A") ? "A",
            tla.name("t_2") ? "b",
            tla.name("B") ? "B",
        )
        .typed(types, "R")
    assert(expected == output)
  }

  test("""A \X B ~~> {<<t_1, t_2>>: t_1 \in A, t_2 \in B}""") {
    val types = Map(
        "a" -> BoolT1,
        "b" -> StrT1,
        "A" -> SetT1(BoolT1),
        "B" -> SetT1(StrT1),
        "t" -> SetT1(TupT1(BoolT1, StrT1)),
        "T" -> SetT1(TupT1(BoolT1, StrT1)),
    )
    val input =
      tla
        .times(tla.name("A") ? "A", tla.name("B") ? "B")
        .typed(types, "T")
    val output = keramelizer.apply(input)
    val tup = tla.tuple(tla.name("t_1") ? "a", tla.name("t_2") ? "b")
    val expected =
      tla
        .map(
            tup ? "t",
            tla.name("t_1") ? "a",
            tla.name("A") ? "A",
            tla.name("t_2") ? "b",
            tla.name("B") ? "B",
        )
        .typed(types, "T")
    assert(expected == output)
  }

  test("""Integer CASE-OTHER becomes IF-THEN-ELSE""") {
    val types = Map("b" -> BoolT1, "i" -> IntT1)
    /*
      CASE p_1 -> e_1
        [] p_2 -> e_2
        OTHER  -> e_def
     */
    val input = tla
      .caseOther(
          tla.name("e_def") ? "i",
          tla.name("p_1") ? "b",
          tla.name("e_1") ? "i",
          tla.name("p_2") ? "b",
          tla.name("e_2") ? "i",
      )
      .typed(types, "i")
    val output = keramelizer.apply(input)

    /**
     * IF p_1 THEN e_1 ELSE IF p_2 THEN e_2 ELSE e_def
     */
    val expected: TlaEx =
      tla
        .ite(tla.name("p_1") ? "b", tla.name("e_1") ? "i",
            tla.ite(tla.name("p_2") ? "b", tla.name("e_2") ? "i", tla.name("e_def") ? "i") ? "b")
        .typed(types, "i")
    assert(expected == output)
  }

  test("""Integer CASE becomes IF-THEN-ELSE""") {
    val types = Map("b" -> BoolT1, "i" -> IntT1)
    /*
      CASE p_1 -> e_1
        [] p_2 -> e_2
     */
    val input = tla
      .caseSplit(tla.name("p_1") ? "b", tla.name("e_1") ? "i", tla.name("p_2") ? "b", tla.name("e_2") ? "i")
      .typed(types, "i")
    val output = keramelizer.apply(input)

    /**
     * We ignore the second guard to extend a partial function to a total function. This is sound, as CASE returns some
     * (unknown) value when no guard holds true.
     *
     * IF p_1 THEN e_1 ELSE e_2
     */
    val expected: TlaEx =
      tla
        .ite(tla.name("p_1") ? "b", tla.name("e_1") ? "i", tla.name("e_2") ? "i")
        .typed(types, "i")
    assert(expected == output)
  }

  test("""Boolean CASE-OTHER becomes a disjunction""") {
    val types = Map("b" -> BoolT1)
    /*
      CASE p_1 -> e_1
        [] p_2 -> e_2
        OTHER  -> e_def
     */
    val input = tla
      .caseOther(
          tla.name("e_def") ? "b",
          tla.name("p_1") ? "b",
          tla.name("e_1") ? "b",
          tla.name("p_2") ? "b",
          tla.name("e_2") ? "b",
      )
      .typed(types, "b")
    val output = keramelizer.apply(input)
    /*
     \/ p_1 /\ e_1
     \/ p_2 /\ e_2
     \/ ~p_1 /\ ~p_2 /\ e_def
     */
    val expected: TlaEx =
      tla
        .or(
            tla.and(tla.name("p_1") ? "b", tla.name("e_1") ? "b") ? "b",
            tla.and(tla.name("p_2") ? "b", tla.name("e_2") ? "b") ? "b",
            tla.and(tla.not(tla.name("p_1") ? "b") ? "b", tla.not(tla.name("p_2") ? "b") ? "b",
                tla.name("e_def") ? "b") ? "b",
        )
        .typed(types, "b")
    assert(expected == output)
  }

  test("""Boolean CASE becomes a disjunction""") {
    val types = Map("b" -> BoolT1)
    /*
      CASE p_1 -> e_1
        [] p_2 -> e_2
        OTHER  -> e_def
     */
    val input = tla
      .caseSplit(tla.name("p_1") ? "b", tla.name("e_1") ? "b", tla.name("p_2") ? "b", tla.name("e_2") ? "b")
      .typed(types, "b")
    val output = keramelizer.apply(input)
    /*
     \/ p_1 /\ e_1
     \/ p_2 /\ e_2
     */
    val expected: TlaEx =
      tla
        .or(
            tla.and(tla.name("p_1") ? "b", tla.name("e_1") ? "b") ? "b",
            tla.and(tla.name("p_2") ? "b", tla.name("e_2") ? "b") ? "b",
        )
        .typed(types, "b")
    assert(expected == output)
  }

  // we simplify assignments into existential quantification
  test("""x' \in S ~~> \E t_1 \in S: x' = t_1""") {
    val types = Map("b" -> BoolT1, "e" -> IntT1, "S" -> SetT1(IntT1))
    val input = tla
      .in(tla.prime(tla.name("x") ? "e") ? "e", tla.name("S") ? "S")
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected: TlaEx =
      tla
        .exists(tla.name("t_1") ? "e", tla.name("S") ? "S",
            tla.eql(tla.prime(tla.name("x") ? "e") ? "e", tla.name("t_1") ? "e") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""x' \in SUBSET S ~~> \E t_1 \in SUBSET S: x' = t_1""") {
    val types = Map("b" -> BoolT1, "S" -> SetT1(IntT1), "PS" -> SetT1(SetT1(IntT1)))
    val input =
      tla
        .in(tla.prime(tla.name("x") ? "S") ? "S", tla.powSet(tla.name("S") ? "S") ? "PS")
        .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected: TlaEx =
      tla
        .exists(tla.name("t_1") ? "S", tla.powSet(tla.name("S") ? "S") ? "PS",
            tla.eql(tla.prime(tla.name("x") ? "S") ? "S", tla.name("t_1") ? "S") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""x' \in [S -> T] ~~> \E t_1 \in [S -> T]: x' = t_1""") {
    val types = Map(
        "b" -> BoolT1,
        "S" -> SetT1(IntT1),
        "T" -> SetT1(StrT1),
        "f" -> FunT1(IntT1, StrT1),
        "Sf" -> SetT1(FunT1(IntT1, StrT1)),
    )
    val funSet = tla.funSet(tla.name("S") ? "S", tla.name("T") ? "T") ? "Sf"
    val input = tla
      .in(tla.prime(tla.name("x") ? "f") ? "f", funSet)
      .typed(types, "b")
    val output = keramelizer.apply(input)
    val expected: TlaEx =
      tla
        .exists(tla.name("t_1") ? "f", funSet,
            tla.eql(tla.prime(tla.name("x") ? "f") ? "f", tla.name("t_1") ? "f") ? "b")
        .typed(types, "b")
    assert(expected == output)
  }

  test("""A \in SUBSET B ~~> \A a \in A: a \in B""") {
    val types = Map("BOOL" -> BoolT1, "POWSET" -> SetT1(SetT1(IntT1)), "SET" -> SetT1(IntT1), "INT" -> IntT1)
    def A = tla.name("A") ? "SET"
    def B = tla.name("B") ? "SET"
    val input =
      tla
        .in(A, tla.powSet(B) ? "POWSET")
        .typed(types, "BOOL")
    val output = keramelizer.apply(input)

    val isExpected = output match {
      // \A element \in A: element \in B
      case OperEx(TlaBoolOper.forall, NameEx(boundName), NameEx("A"),
              OperEx(TlaSetOper.in, NameEx(inName), NameEx("B"))) =>
        boundName == inName
      case _ => false
    }
    assert(isExpected, s"Input $input and got $output")
  }

  test("""A \subseteq B ~~> \A a \in A: a \in B""") {
    val types = Map("BOOL" -> BoolT1, "SET" -> SetT1(IntT1), "INT" -> IntT1)
    def A = tla.name("A") ? "SET"
    def B = tla.name("B") ? "SET"
    val input =
      tla
        .subseteq(A, B)
        .typed(types, "BOOL")
    val output = keramelizer.apply(input)

    val isExpected = output match {
      // \A element \in A: element \in B
      case OperEx(TlaBoolOper.forall, NameEx(boundName), NameEx("A"),
              OperEx(TlaSetOper.in, NameEx(inName), NameEx("B"))) =>
        boundName == inName
      case _ => false
    }
    assert(isExpected, s"Input $input and got $output")
  }

  test("""A \subseteq POWSET POWSET B ~~> \A S \in A: \A T \in S: \A t \in T: t \in B""") {
    val types = Map(
        "BOOL" -> BoolT1,
        "POWPOWSET" -> SetT1(SetT1(SetT1(IntT1))),
        "POWSET" -> SetT1(SetT1(IntT1)),
        "SET" -> SetT1(IntT1),
        "INT" -> IntT1,
    )
    def A = tla.name("A") ? "POWPOWSET"
    def B = tla.name("B") ? "SET"
    def powB = tla.powSet(B) ? "POWSET"
    def powpowB = tla.powSet(powB) ? "POWPOWSET"
    val input =
      tla
        .subseteq(A, powpowB)
        .typed(types, "BOOL")
    val output = keramelizer.apply(input)

    val isExpected = output match {
      // \A outer \in A: \A middle \in outer: \A inner \in middle: inner \in B
      case OperEx(TlaBoolOper.forall, NameEx(outerQuantifier), NameEx("A"),
              OperEx(TlaBoolOper.forall, NameEx(middleQuantifier), NameEx(outerSet),
                  OperEx(TlaBoolOper.forall, NameEx(innerQuantifier), NameEx(middleSet),
                      OperEx(TlaSetOper.in, NameEx(element), NameEx("B"))))) =>
        outerQuantifier == outerSet && middleQuantifier == middleSet && innerQuantifier == element
      case _ => false
    }
    assert(isExpected, s"Input $input and got $output")
  }

  test("""A \subseteq POWSET B ~~> \A S \in A: s \in B""") {
    val types = Map("BOOL" -> BoolT1, "POWSET" -> SetT1(SetT1(IntT1)), "SET" -> SetT1(IntT1), "INT" -> IntT1)
    def A = tla.name("A") ? "POWSET"
    def B = tla.name("B") ? "SET"
    val input =
      tla
        .subseteq(A, tla.powSet(B) ? "POWSET")
        .typed(types, "BOOL")
    val output = keramelizer.apply(input)

    val isExpected = output match {
      // \A outer \in A: \A middle \in outer: \A inner \in middle: inner \in B
      case OperEx(TlaBoolOper.forall, NameEx(outerQuantifier), NameEx("A"),
              OperEx(TlaBoolOper.forall, NameEx(innerQuantifier), NameEx(outerSet),
                  OperEx(TlaSetOper.in, NameEx(element), NameEx("B")))) =>
        outerQuantifier == outerSet && innerQuantifier == element
      case _ => false
    }
    assert(isExpected, s"Input $input and got $output")
  }

  test("""POWSET A \subseteq POWSET B ~~> A \subseteq B ~~> \A a \in A: a \in B""") {
    val types = Map("BOOL" -> BoolT1, "POWSET" -> SetT1(SetT1(IntT1)), "SET" -> SetT1(IntT1), "INT" -> IntT1)
    def A = tla.name("A") ? "SET"
    def B = tla.name("B") ? "SET"
    def powA = tla.powSet(A) ? "POWSET"
    def powB = tla.powSet(B) ? "POWSET"
    val input =
      tla
        .subseteq(powA, powB)
        .typed(types, "BOOL")
    val output = keramelizer.apply(input)
    val isExpected = output match {
      // \A outer \in A: \A middle \in outer: \A inner \in middle: inner \in B
      case OperEx(TlaBoolOper.forall, NameEx(quantifier), NameEx("A"),
              OperEx(TlaSetOper.in, NameEx(element), NameEx("B"))) =>
        quantifier == element
      case _ => false
    }
    assert(isExpected, s"Input $input.toString() and got $output.toString()")

  }

  test("""rewrite f \in [S -> SUBSET T]  ~~>  DOMAIN f = S /\ \A x \in S: \A y \in f[x]: y \in T""".stripMargin) {
    val types =
      Map(
          "b" -> BoolT1,
          "s" -> SetT1(IntT1),
          "p" -> SetT1(SetT1(IntT1)),
          "f" -> FunT1(IntT1, SetT1(IntT1)),
          "fs" -> SetT1(FunT1(IntT1, SetT1(IntT1))),
      )
    val input =
      tla
        .in(tla.name("f") ? "f", tla.funSet(tla.name("S") ? "s", tla.powSet(tla.name("T") ? "s") ? "p") ? "fs")
        .typed(types, "b")
    val output = keramelizer(input)
    val isExpected = output match {
      case OperEx(TlaBoolOper.and, OperEx(TlaOper.eq, OperEx(TlaFunOper.domain, NameEx("f")), NameEx("S")),
              OperEx(TlaBoolOper.forall, NameEx(domElem), NameEx("S"),
                  OperEx(TlaBoolOper.forall, NameEx(cdmElem), OperEx(TlaFunOper.app, NameEx("f"), NameEx(funArg)),
                      OperEx(TlaSetOper.in, NameEx(element), NameEx("T"))))) =>
        domElem == funArg && cdmElem == element
      case _ => false
    }
    assert(isExpected, s"Input $input and got $output")
  }

  test("""rewrite f \in [S -> T]  ~~>  DOMAIN f = S /\ \A x \in S: f[x] \in T""".stripMargin) {
    val types =
      Map("b" -> BoolT1, "s" -> SetT1(IntT1), "f" -> FunT1(IntT1, IntT1), "fs" -> SetT1(FunT1(IntT1, IntT1)))
    val input =
      tla
        .in(tla.name("f") ? "f", tla.funSet(tla.name("S") ? "s", tla.name("T") ? "s") ? "fs")
        .typed(types, "b")
    val output = keramelizer(input)
    val isExpected = output match {
      case OperEx(TlaBoolOper.and, OperEx(TlaOper.eq, OperEx(TlaFunOper.domain, NameEx("f")), NameEx("S")),
              OperEx(TlaBoolOper.forall, NameEx(domElem), NameEx("S"),
                  OperEx(TlaSetOper.in, OperEx(TlaFunOper.app, NameEx("f"), NameEx(funArg)), NameEx("T")))) =>
        domElem == funArg
      case _ => false
    }
    assert(isExpected, s"Input $input and got $output")
  }

  test("simplifies TLA+ expressions to KerA+") {
    // Generator for PBT
    val gens = new IrGenerators { override val maxArgs: Int = 3 }

    // Generated operators
    val ops =
      gens.simpleOperators ++ gens.logicOperators ++ gens.arithOperators ++ gens.setOperators ++ gens.functionOperators

    // Predicates for Keramelizer input and Keramelizer output (= KerA+)
    val inputPred = KeramelizerInputLanguagePred()
    val outputPred = KeraLanguagePred()

    val prop = forAll(gens.genTlaEx(ops)(gens.emptyContext)) { ex =>
      inputPred.isExprOk(ex) == PredResultOk() ==> {
        try {
          val keramelized = keramelizer(ex)
          val inKera = outputPred.isExprOk(keramelized)
          (inKera shouldBe PredResultOk()).withClue(s"when keramelizing $ex to $keramelized")
          true
        } catch {
          // This is a workaround for when `IrGenerators` constructs an ill-typed expressions that fails in Keramelizer,
          // as in #1364.
          // TODO(#1379): Remove this try-catch when we have a well-typing expression generator.
          case _: MalformedTlaError =>
            alert("Ignored MalformedTlaError in PBT")
            true
        }
      }
    }
    check(prop, minSuccessful(500), sizeRange(7))
  }
}
