package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.src.{SourcePosition, SourceRegion}
import at.forsyte.apalache.tla.lir.values._
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

import scala.io.Source

/**
 * A collection of tests that check how SanyImporter loads the standard modules.
 *
 * If you run this test in an IDE and the test fails, set environment variable `APALACHE_HOME` to the root of the
 * Apalache source tree.
 *
 * @author
 *   Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestSanyImporterStandardModules extends SanyImporterTestBase {
  test("EXTENDS of the standard modules") {
    // operators with parameters that are themselves operators with parameters
    val text =
      """---- MODULE imports ----
        |EXTENDS Naturals
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // we strip away the operator declarations by Naturals
    assert(root.declarations.isEmpty)
    // as Naturals containts definitions of the built-in operators, it is empty
    val naturals = modules("Naturals")
    assert(naturals.declarations.isEmpty)
  }

  test("module nats") {
    // check that the Naturals module is imported properly
    val text =
      """---- MODULE nats ----
        |EXTENDS Naturals
        |NatSet == Nat
        |Plus == 3 + 2
        |Minus == 3 - 2
        |Mult == 3 * 2
        |Power == 3 ^ 2
        |Less == 3 < 2
        |Greater == 3 > 2
        |Leq == 3 <= 2
        |Leq2 == 3 =< 2
        |Geq == 3 >= 2
        |Mod == 3 % 2
        |Div == 3 \div 2
        |Range == 2 .. 3
        |
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx): Unit =
      findAndExpectOperDecl(root, name, List(), body)

    // the root module contains its own declarations and the declarations by Naturals
    expectDecl("NatSet", ValEx(TlaNatSet))
    expectDecl(
        "Plus",
        OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Minus",
        OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Mult",
        OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Power",
        OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Less",
        OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Greater",
        OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Leq",
        OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Leq2",
        OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Geq",
        OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Mod",
        OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Div",
        OperEx(TlaArithOper.div, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Range",
        OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3))),
    )

    // check the source info
    root.declarations.find {
      _.name == "Plus"
    } match {
      case Some(TlaOperDecl(_, _, oe @ OperEx(_, _*))) =>
        val loc = sourceStore.find(oe.ID).get
        assert(
            SourceRegion(SourcePosition(4, 9), SourcePosition(4, 13)) == loc.region
        )

      case _ => fail()
    }
  }

  test("module ints") {
    // check that the Integers module is imported properly
    val text =
      """---- MODULE ints ----
        |EXTENDS Integers
        |IntSet == Int
        |Plus == 3 + 2
        |Minus == 3 - 2
        |Mult == 3 * 2
        |Power == 3 ^ 2
        |Less == 3 < 2
        |Greater == 3 > 2
        |Leq == 3 <= 2
        |Geq == 3 >= 2
        |Mod == 3 % 2
        |Div == 3 \div 2
        |Range == 2 .. 3
        |UnaryMinus == -2
        |
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(3 == modules.size) // Integers extends Naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectOperDecl(root, name, List(), body)

    // the definitions of the standard operators are filtered out
    assert(13 == root.declarations.size)

    // the root module contains its own declarations and the declarations by Integers
    expectDecl("IntSet", ValEx(TlaIntSet))
    expectDecl(
        "Plus",
        OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Minus",
        OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Mult",
        OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Power",
        OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Less",
        OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Greater",
        OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Leq",
        OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Geq",
        OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Mod",
        OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Div",
        OperEx(TlaArithOper.div, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Range",
        OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3))),
    )
    expectDecl("UnaryMinus", OperEx(TlaArithOper.uminus, ValEx(TlaInt(2))))
  }

  test("module reals") {
    // check that the Reals module is imported properly
    val text =
      """---- MODULE myreals ----
        |EXTENDS Reals
        |RealSet == Real
        |Inf == Infinity
        |Plus == 3 + 2
        |Minus == 3 - 2
        |Mult == 3 * 2
        |Power == 3 ^ 2
        |Less == 3 < 2
        |Greater == 3 > 2
        |Leq == 3 <= 2
        |Geq == 3 >= 2
        |Mod == 3 % 2
        |Div == 3 \div 2
        |Range == 2 .. 3
        |UnaryMinus == -2
        |RealDiv == 3 / 2
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(4 == modules.size) // Reals include Integers that include Naturals
    val root = modules(rootName)
    // the definitions of the standard operators are filtered out
    assert(15 == root.declarations.size)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectOperDecl(root, name, List(), body)

    expectDecl("RealSet", ValEx(TlaRealSet))
    expectDecl("Inf", ValEx(TlaRealInfinity))
    expectDecl(
        "Plus",
        OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Minus",
        OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Mult",
        OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Power",
        OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Less",
        OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Greater",
        OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Leq",
        OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Geq",
        OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Mod",
        OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Div",
        OperEx(TlaArithOper.div, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
    expectDecl(
        "Range",
        OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3))),
    )
    expectDecl("UnaryMinus", OperEx(TlaArithOper.uminus, ValEx(TlaInt(2))))
    expectDecl(
        "RealDiv",
        OperEx(TlaArithOper.realDiv, ValEx(TlaInt(3)), ValEx(TlaInt(2))),
    )
  }

  test("module seqs") {
    // check that the Sequences module is imported properly
    val text =
      """---- MODULE sequences ----
        |EXTENDS Sequences
        |
        |Empty == <<>>
        |Three == <<1, 2, 3>>
        |ASeq == Seq({1 , 2})
        |ALen == Len(<<1, 2, 3>>)
        |AConcat == <<1, 2>> \o <<3>>
        |AAppend == Append(<<1, 2>>, 3)
        |AHead == Head(<<1, 2, 3>>)
        |ATail == Tail(<<1, 2, 3>>)
        |ASubSeq == SubSeq(<<1, 2, 3, 4>>, 2, 3)
        |Test(i) == i = 2
        |ASelectSeq == SelectSeq(<<1, 2, 3, 4>>, Test)
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(3 == modules.size) // Naturals, Sequences, and our module
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectOperDecl(root, name, List(), body)

    // the definitions of the standard operators are filtered out
    assert(12 == root.declarations.size)

    expectDecl("Empty", tuple())
    expectDecl("Three", tuple(int(1), int(2), int(3)))
    expectDecl("ASeq", seqSet(enumSet(int(1), int(2))))
    expectDecl("ALen", len(tuple(int(1), int(2), int(3))))
    expectDecl("AConcat", concat(tuple(int(1), int(2)), tuple(int(3))))
    expectDecl("AAppend", append(tuple(int(1), int(2)), int(3)))
    expectDecl("AHead", head(tuple(int(1), int(2), int(3))))
    expectDecl("ATail", tail(tuple(int(1), int(2), int(3))))
    expectDecl(
        "ASubSeq",
        subseq(tuple(int(1), int(2), int(3), int(4)), int(2), int(3)),
    )

    // SelectSeq is special as it is rewired with a TLA+ definition
    expectDecl(
        "ASelectSeq",
        OperEx(TlaOper.apply, NameEx("SelectSeq"), tuple(int(1), int(2), int(3), int(4)), name("Test")),
    ) ///
  }

  // FiniteSets
  test("module finitesets") {
    // check that the FiniteSets module is imported properly
    val text =
      """---- MODULE myfinitesets ----
        |EXTENDS FiniteSets
        |IsFinSet == IsFiniteSet(BOOLEAN)
        |Card == Cardinality(BOOLEAN)
        |
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(5 == modules.size) // Naturals, Sequences, FiniteSets, and our module
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectOperDecl(root, name, List(), body)

    // the definitions of the standard operators are filtered out
    assert(2 == root.declarations.size)

    // the root module contains its own declarations and the declarations by FiniteSets
    expectDecl(
        "IsFinSet",
        OperEx(TlaFiniteSetOper.isFiniteSet, ValEx(TlaBoolSet)),
    )
    expectDecl("Card", OperEx(TlaFiniteSetOper.cardinality, ValEx(TlaBoolSet)))
  }

  test("module TLC") {
    // check that the module TLC is imported properly
    val text =
      """---- MODULE tlc ----
        |EXTENDS TLC
        |
        |VARIABLES i
        |
        |APrint == Print("TLC Print", TRUE)
        |APrintT == PrintT("TLC PrintT")
        |AAssert == Assert("TLC Assert", TRUE)
        |AJavaTime == JavaTime
        |ATLCGet == TLCGet(i)
        |ATLCSet == TLCSet(i, 3)
        |AColonGreater == {1, 2} :> 3
        |AtAt == [j \in {1, 2} |-> j] @@ [k \in {3, 4} |-> k]
        |APermutations == Permutations(<<1, 2>>)
        |FakeSort(a, b) == TRUE
        |ASortSeq == SortSeq(<<2, 1>>, FakeSort)
        |ARandomElement == RandomElement({1, 2})
        |AAny == Any
        |AToString == ToString(42)
        |ATLCEval == TLCEval(42)
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    // the root module and integers
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx): Unit =
      findAndExpectOperDecl(root, name, List(), body)

    // the definitions of tlc and TLC
    assert(30 == root.declarations.size)

    expectDecl("APrint", OperEx(TlaOper.apply, NameEx("Print"), str("TLC Print"), bool(true)))
    expectDecl("APrintT", OperEx(TlaOper.apply, NameEx("PrintT"), str("TLC PrintT")))
    expectDecl("AAssert", OperEx(TlaOper.apply, NameEx("Assert"), str("TLC Assert"), bool(true)))
    expectDecl("AJavaTime", OperEx(TlaOper.apply, NameEx("JavaTime")))
    expectDecl("ATLCGet", OperEx(TlaOper.apply, NameEx("TLCGet"), name("i")))
    expectDecl("ATLCSet", OperEx(TlaOper.apply, NameEx("TLCSet"), name("i"), int(3)))
    expectDecl(
        "AColonGreater",
        OperEx(TlaOper.apply, NameEx(":>"), enumSet(int(1), int(2)), int(3)),
    )
    val fun12 = funDef(name("j"), name("j"), enumSet(int(1), int(2)))
    val fun34 = funDef(name("k"), name("k"), enumSet(int(3), int(4)))
    expectDecl("AtAt", OperEx(TlaOper.apply, NameEx("@@"), fun12, fun34))
    expectDecl(
        "APermutations",
        OperEx(TlaOper.apply, NameEx("Permutations"), tuple(int(1), int(2))),
    )
    expectDecl(
        "ASortSeq",
        OperEx(TlaOper.apply, NameEx("SortSeq"), tuple(int(2), int(1)), name("FakeSort")),
    )
    expectDecl(
        "ARandomElement",
        OperEx(TlaOper.apply, NameEx("RandomElement"), enumSet(int(1), int(2))),
    )
    expectDecl("AAny", OperEx(TlaOper.apply, NameEx("Any")))
    expectDecl("ATLCEval", OperEx(TlaOper.apply, NameEx("TLCEval"), int(42)))
    expectDecl("AToString", OperEx(TlaOper.apply, NameEx("ToString"), int(42)))
  }

  test("EXTENDS Bags") {
    // currently, Bags is imported as a user-defined module, no built-in operators are introduced
    val text =
      """---- MODULE localSum ----
        |EXTENDS Bags
        |================================
      """.stripMargin

    val (_, modules) = sanyImporter.loadFromSource(Source.fromString(text))
    assert(6 == modules.size) // Naturals, Sequences, TLC, FiniteSets, Bags, and our module

    val root = modules("localSum")
    expectSourceInfoInDefs(root)
    // This number may change when a new version of Bags.tla is shipped in tla2tools.jar.
    // The declarations include the declarations by __rewire_tlc_in_apalache.tla and Bags.tla.
    assert(13 == root.declarations.size)
  }

  test("EXTENDS Apalache") {
    val text =
      """---- MODULE root ----
        |EXTENDS Integers, FiniteSets, Apalache
        |VARIABLE x, S
        |
        |Assn == x' := 1
        |Sklm == Skolem(\E y \in S: TRUE)
        |Gss == Guess(S)
        |Expnd == Expand(SUBSET S)
        |CC == ConstCardinality(Cardinality(S) >= 2)
        |Identity(i) == i
        |Seq2to11 == MkSeq(10, Identity)
        |================================
      """.stripMargin

    // If you run this test in an IDE and the test fails, set environment variable `APALACHE_HOME` to the root of the
    // Apalache source tree.

    val (_, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))
    assert(7 == modules.size) // root, Apalache, Integers, FiniteSets, and whatever they import

    val root = modules("root")
    expectSourceInfoInDefs(root)
    assert(10 == root.declarations.size)

    def expectDecl(name: String, body: TlaEx): Unit = {
      findAndExpectOperDecl(root, name, List(), body)
    }

    expectDecl(
        "Assn",
        OperEx(
            ApalacheOper.assign,
            OperEx(TlaActionOper.prime, NameEx("x")),
            ValEx(TlaInt(1)),
        ),
    )
    expectDecl(
        "Sklm",
        OperEx(
            ApalacheOper.skolem,
            OperEx(
                TlaBoolOper.exists,
                NameEx("y"),
                NameEx("S"),
                ValEx(TlaBool(true)),
            ),
        ),
    )
    expectDecl(
        "Gss",
        OperEx(
            ApalacheOper.guess,
            NameEx("S"),
        ),
    )
    expectDecl(
        "Expnd",
        OperEx(ApalacheOper.expand, OperEx(TlaSetOper.powerset, NameEx("S"))),
    )
    expectDecl(
        "CC",
        OperEx(
            ApalacheOper.constCard,
            OperEx(
                TlaArithOper.ge,
                OperEx(TlaFiniteSetOper.cardinality, NameEx("S")),
                ValEx(TlaInt(2)),
            ),
        ),
    )
    expectDecl(
        "Seq2to11",
        OperEx(ApalacheOper.mkSeq, ValEx(TlaInt(10)), NameEx("Identity")),
    )
  }

  test("EXTENDS Variants") {
    val text =
      """---- MODULE root ----
        |EXTENDS Integers, FiniteSets, Variants
        |
        |\* @type: () => T1a({ val: Int, found: Bool });
        |TestVariant == Variant("T1a", [ val |-> 3, found |-> FALSE ])
        |
        |\* @type: Set(T1a({ val: Int, found: Bool) | T2a({ bal: Int })) => Set({ val: Int, found: Bool });
        |TestVariantFilter == VariantFilter("T1a", { TestVariant })
        |
        |\* @type: T1a({ val: Int, found: Bool }) => Str;
        |TestVariantTag(var) ==
        |  VariantTag(var)
        |
        |\* @type: T1a({ val: Int, found: Bool }) => { val: Int, found: Bool };
        |TestVariantGetUnsafe(var) ==
        |  VariantGetUnsafe("T1a", var)
        |
        |\* @type: (T1a({ val: Int, found: Bool }), { val: Int, found: Bool }) => { val: Int, found: Bool };
        |TestVariantGetOrElse(var) ==
        |  VariantGetOrElse("T1a", var, [ val |-> 0, found |-> FALSE])
        |================================
      """.stripMargin

    // If you run this test in an IDE and the test fails, set environment variable `APALACHE_HOME` to the root of the
    // Apalache source tree.

    val (_, modules) = sanyImporter
      .loadFromSource(Source.fromString(text))

    val root = modules("root")
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx, params: OperParam*): Unit = {
      findAndExpectOperDecl(root, name, params.toList, body)
    }

    // TestVariant == Variant("T1a", [ val |-> 3, found |-> FALSE ])
    expectDecl(
        "TestVariant",
        OperEx(
            VariantOper.variant,
            ValEx(TlaStr("T1a")),
            OperEx(
                TlaFunOper.rec,
                ValEx(TlaStr("val")),
                ValEx(TlaInt(3)),
                ValEx(TlaStr("found")),
                ValEx(TlaBool(false)),
            ),
        ),
    )

    // TestVariantFilter == VariantFilter("T1a", { Var })
    expectDecl(
        "TestVariantFilter",
        OperEx(
            VariantOper.variantFilter,
            ValEx(TlaStr("T1a")),
            OperEx(TlaSetOper.enumSet, OperEx(TlaOper.apply, NameEx("TestVariant"))),
        ),
    )

    // TestVariantTag(var) ==
    //   VariantTag("T1a", var)
    val applyMatchOnly =
      OperEx(
          VariantOper.variantTag,
          name("var"),
      )

    expectDecl(
        "TestVariantTag",
        applyMatchOnly,
        OperParam("var"),
    )

    // TestVariantGetUnsafe(var) == VariantGetUnsafe("T1a", var)
    expectDecl(
        "TestVariantGetUnsafe",
        OperEx(
            VariantOper.variantGetUnsafe,
            ValEx(TlaStr("T1a")),
            NameEx("var"),
        ),
        OperParam("var"),
    )

    // TestVariantGetOrElse(var) ==
    //  VariantGetOrElse("T1a", var, [ val |-> 0, found |-> FALSE])
    expectDecl(
        "TestVariantGetOrElse",
        OperEx(
            VariantOper.variantGetOrElse,
            ValEx(TlaStr("T1a")),
            NameEx("var"),
            OperEx(
                TlaFunOper.rec,
                ValEx(TlaStr("val")),
                ValEx(TlaInt(0)),
                ValEx(TlaStr("found")),
                ValEx(TlaBool(false)),
            ),
        ),
        OperParam("var"),
    )
  }
}
