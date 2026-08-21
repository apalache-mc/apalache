package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.lir.{PrettyWriter, TextLayout}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.{TlaEx, TlaOperDecl}

import java.io.{PrintWriter, StringWriter}
import scala.io.Source

class TestPrettyWriterPrecedence extends SanyImporterTestBase {
  private def write(ex: TlaEx): String = {
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    new PrettyWriter(printWriter, TextLayout().copy(textWidth = 80)).write(ex)
    printWriter.flush()
    stringWriter.toString
  }

  test("precedence conflicts are parenthesized and round-trip through SANY") {
    val cases: Seq[(TlaEx, String)] = Seq(
        (eql(comp(name("a"), name("b")), name("c")), "(a \\cdot b) = c"),
        (eql(name("a"), comp(name("b"), name("c"))), "a = (b \\cdot c)"),
        (times(union(name("S")), name("T")), "(UNION S) \\X T"),
        (times(name("S"), union(name("T"))), "S \\X (UNION T)"),
        (times(powSet(name("S")), name("T")), "(SUBSET S) \\X T"),
        (times(name("S"), powSet(name("T"))), "S \\X (SUBSET T)"),
        (times(dom(name("S")), name("T")), "(DOMAIN S) \\X T"),
        (times(name("S"), dom(name("T"))), "S \\X (DOMAIN T)"),
    )

    cases.zipWithIndex.foreach { case ((original, expected), index) =>
      withClue(s"case $index: ") {
        val printed = write(original)
        assert(printed == expected)

        val moduleName = s"PrecedenceRoundTrip$index"
        val source =
          s"""---- MODULE $moduleName ----
             |CONSTANTS a, b, c, S, T
             |Test == $printed
             |================================
             |""".stripMargin
        val (rootName, modules) = sanyImporter.loadFromSource(Source.fromString(source))
        val parsed = modules(rootName).declarations
          .collectFirst {
            case decl: TlaOperDecl if decl.name == "Test" => decl.body
          }
          .getOrElse(fail("SANY did not import the Test declaration"))

        assert(parsed == original)
      }
    }
  }
}
