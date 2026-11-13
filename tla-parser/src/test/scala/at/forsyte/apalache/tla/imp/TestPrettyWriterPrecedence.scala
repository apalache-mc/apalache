package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.lir.{PrettyWriter, TextLayout}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla.{not => tlaNot, _}
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.{OperEx, OperParam, TlaEx, TlaOperDecl}

import java.io.{PrintWriter, StringWriter}
import scala.io.Source

class TestPrettyWriterPrecedence extends SanyImporterTestBase {
  private case class RoundTripCase(
      label: String,
      original: TlaEx,
      expectedText: String,
      expectedParsed: TlaEx)

  private def write(ex: TlaEx, width: Int = 80): String = {
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    new PrettyWriter(printWriter, TextLayout().copy(textWidth = width)).write(ex)
    printWriter.flush()
    stringWriter.toString
  }

  private def equalRoundTripCase(label: String, original: TlaEx, expectedText: String): RoundTripCase =
    RoundTripCase(label, original, expectedText, original)

  private def assertRoundTrips(cases: Seq[RoundTripCase], moduleNamePrefix: String): Unit = {
    cases.zipWithIndex.foreach { case (testCase, index) =>
      withClue(s"${testCase.label}: ") {
        val printed = write(testCase.original)
        assert(printed == testCase.expectedText)

        val moduleName = s"$moduleNamePrefix$index"
        val source =
          s"""---- MODULE $moduleName ----
             |EXTENDS Integers, Sequences
             |VARIABLES a, b, c, S, T, x, y
             |Test == $printed
             |================================
             |""".stripMargin
        assert(parseTestBody(source) == testCase.expectedParsed)
      }
    }
  }

  private def parseTestBody(source: String): TlaEx = {
    val (rootName, modules) = sanyImporter.loadFromSource(Source.fromString(source))
    modules(rootName).declarations
      .collectFirst {
        case decl: TlaOperDecl if decl.name == "Test" => decl.body
      }
      .getOrElse(fail("SANY did not import the Test declaration"))
  }

  for {
    named <- Seq(false, true)
    multipleDecls <- Seq(false, true)
    width <- Seq(20, 1000)
  } {
    test(s"synthesized LET preserves scope through SANY (named=$named, multiple=$multipleDecls, width=$width)") {
      val lambdaDecl = TlaOperDecl("Lambda3", List(OperParam("p"), OperParam("q")), name("p"))
      val seedDecl = TlaOperDecl("Seed", List.empty, bool(false))
      val lambda = letIn(name("Lambda3"), lambdaDecl)
      val seed = if (multipleDecls) letIn(appDecl(seedDecl), seedDecl) else bool(false)

      def call(operatorArg: TlaEx, seedArg: TlaEx): TlaEx =
        if (named) appOp(name("Fold"), operatorArg, seedArg, tuple())
        else OperEx(ApalacheOper.foldSeq, operatorArg, seedArg, tuple())

      val original = call(lambda, seed)
      // The printer hoists argument-local definitions. SANY should recover that hoisted tree,
      // not the original argument-local LETs, and must not move any surrounding operands into it.
      val expectedBody = call(name("Lambda3"), if (multipleDecls) appDecl(seedDecl) else bool(false))
      val expected = letIn(if (multipleDecls) letIn(expectedBody, seedDecl) else expectedBody, lambdaDecl)
      val contexts: Seq[(String, TlaEx => TlaEx)] = Seq(
          ("top level", ex => ex),
          ("issue 88", ex => and(eql(name("var0"), ex), eql(name("step"), int(0)))),
          ("conjunction", ex => and(ex, eql(name("step"), int(0)))),
          ("implication", ex => impl(eql(name("var0"), ex), eql(name("step"), int(0)))),
          ("membership", ex => and(in(ex, enumSet(bool(false))), eql(name("step"), int(0)))),
          ("CASE OTHER", ex => and(caseOther(ex, bool(true), bool(false)), eql(name("step"), int(0)))),
          ("IF branch", ex => and(ite(bool(true), ex, bool(false)), eql(name("step"), int(0)))),
      )
      contexts.zipWithIndex.foreach { case ((label, context), index) =>
        val printed = write(context(original), width)
        val source =
          s"""---- MODULE SynthesizedLet$index ----
             |EXTENDS Integers, Sequences, Apalache
             |VARIABLES var0, step
             |Fold(Op(_, _), initial, seq) == ApaFoldSeqLeft(Op, initial, seq)
             |Test == $printed
             |================================
             |""".stripMargin
        withClue(s"$label: $printed\n") {
          assert(parseTestBody(source) == context(expected))
        }
      }
    }
  }

  test("precedence conflicts are parenthesized and round-trip through SANY") {
    val cases = Seq(
        equalRoundTripCase("composition on the left of equality", eql(comp(name("a"), name("b")), name("c")),
            "(a \\cdot b) = c"),
        equalRoundTripCase("composition on the right of equality", eql(name("a"), comp(name("b"), name("c"))),
            "a = (b \\cdot c)"),
        equalRoundTripCase("UNION on the left of product", times(union(name("S")), name("T")), "(UNION S) \\X T"),
        equalRoundTripCase("UNION on the right of product", times(name("S"), union(name("T"))), "S \\X (UNION T)"),
        equalRoundTripCase("SUBSET on the left of product", times(powSet(name("S")), name("T")), "(SUBSET S) \\X T"),
        equalRoundTripCase("SUBSET on the right of product", times(name("S"), powSet(name("T"))), "S \\X (SUBSET T)"),
        equalRoundTripCase("DOMAIN on the left of product", times(dom(name("S")), name("T")), "(DOMAIN S) \\X T"),
        equalRoundTripCase("DOMAIN on the right of product", times(name("S"), dom(name("T"))), "S \\X (DOMAIN T)"),
    )

    assertRoundTrips(cases, "PrecedenceRoundTrip")
  }

  test("SUBSET and UNION conflicts with set operators round-trip through SANY") {
    val unaryOperators: Seq[(String, TlaEx => TlaEx)] = Seq(
        ("SUBSET", ex => powSet(ex)),
        ("UNION", ex => union(ex)),
    )
    val binaryOperators: Seq[(String, (TlaEx, TlaEx) => TlaEx)] = Seq(
        ("\\union", (lhs, rhs) => cup(lhs, rhs)),
        ("\\intersect", (lhs, rhs) => cap(lhs, rhs)),
        ("\\", (lhs, rhs) => setminus(lhs, rhs)),
    )
    val cases = for {
      (operatorName, applyUnary) <- unaryOperators
      (binaryOperatorName, applyBinary) <- binaryOperators
      testCase <- Seq(
          equalRoundTripCase(s"$operatorName on the left of $binaryOperatorName",
              applyBinary(applyUnary(name("S")), name("T")), s"($operatorName S) $binaryOperatorName T"),
          equalRoundTripCase(s"$operatorName on the right of $binaryOperatorName",
              applyBinary(name("S"), applyUnary(name("T"))), s"S $binaryOperatorName ($operatorName T)"),
          equalRoundTripCase(s"$operatorName over $binaryOperatorName", applyUnary(applyBinary(name("S"), name("T"))),
              s"$operatorName (S $binaryOperatorName T)"),
      )
    } yield testCase

    assertRoundTrips(cases, "SetPrefixRoundTrip")
  }

  test("set and function operators preserve interval and arithmetic grouping through SANY") {
    val unaryOperators: Seq[(String, TlaEx => TlaEx)] = Seq(
        ("SUBSET", ex => powSet(ex)),
        ("UNION", ex => union(ex)),
        ("DOMAIN", ex => dom(ex)),
    )
    val cases = unaryOperators.flatMap { case (operatorName, applyUnary) =>
      Seq(
          equalRoundTripCase(s"$operatorName on the left of interval", dotdot(applyUnary(name("S")), name("T")),
              s"($operatorName S) .. T"),
          equalRoundTripCase(s"$operatorName on the right of interval", dotdot(name("S"), applyUnary(name("T"))),
              s"S .. ($operatorName T)"),
          equalRoundTripCase(s"$operatorName over interval", applyUnary(dotdot(int(1), int(3))),
              s"$operatorName (1 .. 3)"),
          equalRoundTripCase(s"$operatorName on the left of addition", plus(applyUnary(name("S")), name("T")),
              s"($operatorName S) + T"),
          equalRoundTripCase(s"$operatorName on the right of addition", plus(name("S"), applyUnary(name("T"))),
              s"S + ($operatorName T)"),
          equalRoundTripCase(s"$operatorName over addition", applyUnary(plus(name("S"), name("T"))),
              s"$operatorName (S + T)"),
      )
    }

    assertRoundTrips(cases, "SetPrefixBindingRoundTrip")
  }

  test("nested set and function operators round-trip through SANY") {
    val unaryOperators: Seq[(String, Int, TlaEx => TlaEx)] = Seq(
        ("SUBSET", 80, ex => powSet(ex)),
        ("UNION", 80, ex => union(ex)),
        ("DOMAIN", 90, ex => dom(ex)),
    )
    val cases = for {
      (outerOperatorName, outerPrecedence, applyOuterOperator) <- unaryOperators
      (innerOperatorName, innerPrecedence, applyInnerOperator) <- unaryOperators
      innerExpressionText = s"$innerOperatorName S"
      operandText = if (innerPrecedence > outerPrecedence) innerExpressionText else s"($innerExpressionText)"
    } yield equalRoundTripCase(s"$outerOperatorName over $innerOperatorName",
        applyOuterOperator(applyInnerOperator(name("S"))), s"$outerOperatorName $operandText")

    assertRoundTrips(cases, "NestedSetPrefixRoundTrip")
  }

  test("unbounded binders use TLA+ syntax and round-trip through SANY") {
    val chooseEx = choose(name("z"), bool(true))
    val forallEx = forall(name("z"), bool(false))
    val existsEx = exists(name("z"), bool(false))
    val cases = Seq(
        equalRoundTripCase("unbounded CHOOSE", chooseEx, "CHOOSE z : TRUE"),
        equalRoundTripCase("unbounded forall", forallEx, "\\A z : FALSE"),
        equalRoundTripCase("unbounded exists", existsEx, "\\E z : FALSE"),
        equalRoundTripCase("unbounded CHOOSE under equality", eql(chooseEx, name("y")), "(CHOOSE z : TRUE) = y"),
        equalRoundTripCase("unbounded forall under equality", eql(forallEx, bool(true)), "(\\A z : FALSE) = TRUE"),
        equalRoundTripCase("unbounded exists under equality", eql(existsEx, bool(true)), "(\\E z : FALSE) = TRUE"),
    )

    assertRoundTrips(cases, "UnboundedBinderRoundTrip")
  }

  test("action and fairness subscripts use TLA+ delimiters and round-trip through SANY") {
    val action = bool(false)
    val actionSubscript = head(tuple())
    val cases = Seq(
        equalRoundTripCase("stuttering action with a bare subscript", stutt(action, name("x")), "[FALSE]_x"),
        equalRoundTripCase("non-stuttering action with a bare subscript", nostutt(action, name("x")), "<<FALSE>>_x"),
        equalRoundTripCase("weak fairness with a bare subscript", WF(name("x"), action), "WF_x(FALSE)"),
        equalRoundTripCase("strong fairness with a bare subscript", SF(name("x"), action), "SF_x(FALSE)"),
        equalRoundTripCase("stuttering action with a grouped subscript", stutt(action, actionSubscript),
            "[FALSE]_(Head(<<>>))"),
        equalRoundTripCase("non-stuttering action with a grouped subscript", nostutt(action, actionSubscript),
            "<<FALSE>>_(Head(<<>>))"),
        equalRoundTripCase("weak fairness with a grouped subscript", WF(int(0), action), "WF_(0)(FALSE)"),
        equalRoundTripCase("strong fairness with a grouped subscript", SF(int(0), action), "SF_(0)(FALSE)"),
        equalRoundTripCase("non-stuttering action with a Boolean subscript", nostutt(action, bool(false)),
            "<<FALSE>>_FALSE"),
    )

    assertRoundTrips(cases, "ActionSubscriptRoundTrip")
  }

  test("embedded labels are parenthesized and round-trip through SANY") {
    val labelledTuple = label(tuple(), "label0")
    val issueExample = in(concat(tuple(), label(concat(tuple(), tuple()), "label0")), enumSet())
    val cases = Seq(
        equalRoundTripCase("issue example", issueExample, "<<>> \\o (label0 :: (<<>> \\o <<>>)) \\in {}"),
        equalRoundTripCase("label on the left of an infix operator", concat(labelledTuple, tuple()),
            "(label0 :: <<>>) \\o <<>>"),
        equalRoundTripCase("label on the right of an infix operator", concat(tuple(), labelledTuple),
            "<<>> \\o (label0 :: <<>>)"),
        equalRoundTripCase("label as a membership operand", in(label(name("x"), "label0"), name("S")),
            "(label0 :: x) \\in S"),
        equalRoundTripCase("label as a function expression", appFun(label(name("a"), "label0"), int(1)),
            "(label0 :: a)[1]"),
        equalRoundTripCase("label as a function argument", appFun(name("a"), label(int(1), "label0")),
            "a[(label0 :: 1)]"),
        equalRoundTripCase("label under a prefix operator", enabled(label(bool(false), "label0")),
            "ENABLED (label0 :: FALSE)"),
    )

    assertRoundTrips(cases, "LabelRoundTrip")
  }

  test("parenthesized set-map bodies round-trip through SANY") {
    val scalarBody = in(tlaNot(bool(false)), name("S"))
    val tupleBody = in(tuple(name("x"), name("y")), name("S"))
    val ordinaryMap = map(plus(name("u"), name("v")), name("u"), name("S"), name("v"), name("T"))
    val nestedMap = map(map(in(name("x"), name("S")), name("u"), name("T")), name("v"), name("S"))
    val wrappedMembership = in(name("z"), enumSet(int(1)))
    val compoundMembership = in(plus(name("z"), int(0)), enumSet(int(1)))
    val canonicalWrappedMap = map(wrappedMembership, name("z"), enumSet(int(2)))
    val canonicalCompoundMap = map(compoundMembership, name("z"), enumSet(int(2)))
    val cases = Seq(
        equalRoundTripCase("ordinary map with multiple binders", ordinaryMap, "{ (u + v): u \\in S, v \\in T }"),
        equalRoundTripCase("scalar membership body", map(scalarBody, name("z"), name("T")),
            "{ ((~FALSE) \\in S): z \\in T }"),
        equalRoundTripCase("tuple membership body", map(tupleBody, name("z"), name("T")),
            "{ (<<x, y>> \\in S): z \\in T }"),
        equalRoundTripCase("nested map body", nestedMap, "{ ({ (x \\in S): u \\in T }): v \\in S }"),
        RoundTripCase(
            "membership under singleton conjunction",
            map(and(wrappedMembership), name("z"), enumSet(int(2))),
            "{ (z \\in {1}): z \\in {2} }",
            canonicalWrappedMap,
        ),
        RoundTripCase(
            "membership under singleton disjunction",
            map(or(wrappedMembership), name("z"), enumSet(int(2))),
            "{ (z \\in {1}): z \\in {2} }",
            canonicalWrappedMap,
        ),
        RoundTripCase(
            "compound membership under singleton conjunction",
            map(and(compoundMembership), name("z"), enumSet(int(2))),
            "{ (z + 0 \\in {1}): z \\in {2} }",
            canonicalCompoundMap,
        ),
    )

    assertRoundTrips(cases, "SetMapBodyRoundTrip")
  }

  test("prefix operands are parenthesized and round-trip through SANY") {
    val prefixes: Seq[(String, String, TlaEx => TlaEx)] = Seq(
        ("ENABLED", "ENABLED ", arg => enabled(arg)),
        ("UNCHANGED", "UNCHANGED ", arg => unchanged(arg)),
        ("diamond", "<>", arg => diamond(arg)),
        ("box", "[]", arg => box(arg)),
    )
    val operands: Seq[(String, TlaEx, String)] = Seq(
        ("prime", prime(name("x")), "x'"),
        ("equality", eql(name("x"), bool(false)), "x = FALSE"),
        ("inequality", neql(name("x"), bool(false)), "x /= FALSE"),
        ("membership", in(name("x"), name("S")), "x \\in S"),
        ("non-membership", notin(name("x"), name("S")), "x \\notin S"),
    )
    val cases = for {
      (prefixLabel, prefixText, prefix) <- prefixes
      (operandLabel, operand, operandText) <- operands
      // Apart from ENABLED, SANY parses these prime cases but rejects them during semantic level checking.
      // TestPrettyWriter covers their exact output.
      if operandLabel != "prime" || prefixLabel == "ENABLED"
      original = prefix(operand)
    } yield equalRoundTripCase(s"$prefixLabel over $operandLabel", original, s"$prefixText($operandText)")

    assertRoundTrips(cases, "PrefixRoundTrip")
  }

  test("negative integer literals are parenthesized and parse through SANY") {
    val cases = Seq(
        RoundTripCase("top-level negative integer", int(-1), "-1", uminus(int(1))),
        RoundTripCase("negative exponent", exp(int(2), int(-1)), "2 ^ (-1)", exp(int(2), uminus(int(1)))),
        RoundTripCase("negative multiplier", mult(int(2), int(-1)), "2 * (-1)", mult(int(2), uminus(int(1)))),
        RoundTripCase("negative divisor", div(int(2), int(-1)), "2 \\div (-1)", div(int(2), uminus(int(1)))),
        RoundTripCase("unary minus of a negative integer", uminus(int(-106)), "-(-106)", uminus(uminus(int(106)))),
    )

    assertRoundTrips(cases, "NegativeRoundTrip")
  }
}
