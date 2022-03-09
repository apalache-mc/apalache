package at.forsyte.apalache.io.annotations

import at.forsyte.apalache.io.annotations.parser.CommentPreprocessor
import org.junit.runner.RunWith
import org.scalacheck.Gen.asciiStr
import org.scalacheck.Prop.forAll
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
class TestCommentPreprocessor extends AnyFunSuite with Checkers {

  test("test on empty input") {
    val (output, potentialAnnotations) = CommentPreprocessor()("")
    assert(output == "")
    assert(potentialAnnotations.isEmpty)
  }

  test("remove \\*") {
    val input =
      """\* T-Rex
        |\* D-Rex
        |""".stripMargin
    val (output, potentialAnnotations) = CommentPreprocessor()(input)
    val expected =
      """ T-Rex
        | D-Rex
        |""".stripMargin
    assert(output == expected)
    assert(potentialAnnotations.isEmpty)
  }

  test("don't touch the quote") {
    // a bug found by ScalaCheck
    val input =
      """" " """.stripMargin
    val (output, potentialAnnotations) = CommentPreprocessor()(input)
    val expected =
      """ " """".stripMargin
    assert(output.trim == expected.trim)
    assert(potentialAnnotations.isEmpty)
  }

  test("remove (*...*)") {
    val input =
      """(* T-Rex
        |   D-Rex*)
        |   (* zz.*)
        | (* \* uuuuvvv*)abc
        |(*
        |  aaaa (* bbbb *) cccc
        | *)
        |""".stripMargin
    val (output, potentialAnnotations) = CommentPreprocessor()(input)
    val expected =
      """ T-Rex
        |   D-Rex
        |    zz.
        |  abc
        |
        |  aaaa  cccc
        | 
        |""".stripMargin
    assert(output == expected)
    assert(potentialAnnotations.isEmpty)
  }

  test("extract @annotation(...)") {
    val input =
      """\* @annotation("a", 1) (aaa)
        |\* not an annotation: john@example.org
        |\* @semi: foo ; xxx
        |\* @multi: aaa
        |\* bbb
        |\* ccc;ddd
        |\* zzz@bbb(1)
        |""".stripMargin
    val (output, potentialAnnotations) = CommentPreprocessor()(input)
    val expected =
      """ (aaa)
        | not an annotation: john@example.org
        | xxx
        |ddd
        | zzz@bbb(1)
        |""".stripMargin
    assert(output == expected)
    assert(potentialAnnotations == List("@annotation(\"a\", 1)", "@semi: foo ;", "@multi: aaa bbb ccc;"))
  }

  test("unclosed annotations") {
    val input =
      """\* xx @annotation("a",
        |(* aaa @semi: bar *)
        |""".stripMargin
    val (output, potentialAnnotations) = CommentPreprocessor()(input)
    val expected =
      """ xx: bar 
        |""".stripMargin
    assert(output == expected)
    // The extracted annotation is ill-formed. This will be detected by the annotation parser.
    assert(potentialAnnotations == List("@annotation(\"a\", aaa @semi"))
  }

  test("annotations in strings") {
    val input =
      """\* @adventurous("@IgnoreMe(false, 42)", 1) (aaa)
        |\* @beware: of :) ;
        |\* type annotation @type: Set(Set(a)) ;
        |\* @type: a
        |\*          => Int
        |\* ;
        |""".stripMargin
    val (output, potentialAnnotations) = CommentPreprocessor()(input)
    val expected =
      """ (aaa)
        |
        | type annotation
        |
        |""".stripMargin
    assert(output == expected)
    assert(potentialAnnotations.size == 4)
    assert(potentialAnnotations.head == "@adventurous(\"@IgnoreMe(false, 42)\", 1)")
    assert(potentialAnnotations(1) == "@beware: of :) ;")
    assert(potentialAnnotations(2) == "@type: Set(Set(a)) ;")
    assert(potentialAnnotations(3) == "@type: a          => Int ;")
  }

  test("Single-line comment only") {
    hasAnnotationsWhenNonEmpty("""\*""")
  }

  test("Multi-line comment only") {
    hasAnnotationsWhenNonEmpty("""(* aaa *)""")
  }

  test("no failure on random inputs") {
    check(
        {
          forAll(asciiStr) { str =>
            hasAnnotationsWhenNonEmpty(str)
          // no exceptions
          }
        },
        minSuccessful(300),
    )
  }

  private def hasAnnotationsWhenNonEmpty(str: String): Boolean = {
    val (text, annotations) = CommentPreprocessor()(str)
    // replace the comment literals with empty strings
    val noComments = str.replaceAll("""(\\\*|\(\*|\*\))""", "").trim
    noComments.nonEmpty == (text.trim().nonEmpty || annotations.nonEmpty)
  }
}
