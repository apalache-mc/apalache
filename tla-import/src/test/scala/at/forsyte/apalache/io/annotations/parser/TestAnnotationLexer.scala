package at.forsyte.apalache.io.annotations.parser

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import java.io.StringReader

/**
 * Tests for the TLC configuration parser. As the lexer does not know the syntactic structure of annotations,
 * it may produce additional tokens that have to be resolved by the parser.
 *
 * @author Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestAnnotationLexer extends FunSuite {
  test("empty") {
    val text = "   "
    val output = AnnotationLexer.apply(new StringReader(text))
    assert(output.isEmpty)
  }

  test("@test") {
    val text = "(*  @test *)"
    val output = AnnotationLexer.apply(new StringReader(text))
    assert(List(AT_IDENT("test")) == output)
  }

  test("@test(123, TRUE)") {
    val text = "  @test(123, TRUE) "
    val output = AnnotationLexer.apply(new StringReader(text)).toList
    val expected = List(AT_IDENT("test"), LPAREN(), NUMBER(123), COMMA(), BOOLEAN(true), RPAREN())
    assert(expected == output)
  }

  test("an annotation surrounded by some text") {
    val text = """\* example by foo@example.org: @test(123, TRUE) the rest is junk. :-)"""
    val output = AnnotationLexer.apply(new StringReader(text)).toList
    val expected =
      List(IDENT("example"), IDENT("by"), IDENT("foo"), AT_IDENT("example"), DOT(), IDENT("org"), AT_IDENT("test"),
          LPAREN(), NUMBER(123), COMMA(), BOOLEAN(true), RPAREN(), IDENT("the"), IDENT("rest"), IDENT("is"),
          IDENT("junk"), DOT())
    assert(expected == output)
  }

  test("identifier argument") {
    val text = """@foo(Bar)"""
    val output = AnnotationLexer.apply(new StringReader(text)).toList
    val expected = List(AT_IDENT("foo"), LPAREN(), IDENT("Bar"), RPAREN())
    assert(expected == output)
  }

  test("string argument") {
    val text = """@foo("one", "two")"""
    val output = AnnotationLexer.apply(new StringReader(text)).toList
    val expected =
      List(AT_IDENT("foo"), LPAREN(), STRING("one"), COMMA(), STRING("two"), RPAREN())
    assert(expected == output)
  }

  test("inline string argument") {
    val text = """@baz: one;"""
    val output = AnnotationLexer.apply(new StringReader(text)).toList
    val expected = List(AT_IDENT("baz"), INLINE_STRING(" one"))
    assert(expected == output)
  }

  test("mismatch in a string") {
    val text = """ 1.3 " zzz """
    val output = AnnotationLexer.apply(new StringReader(text)).toList
    val expected = List(NUMBER(1), DOT(), NUMBER(3))
    assert(expected == output)
  }

  test("annotation with comments inside") {
    // It should be possible to write a multiline string using the ":...;" syntax.
    // As such a string would be inside a TLA+ comment, we have to remove the leading comment characters.
    val text =
      """\* @type: Int
      |\*          => Int;""".stripMargin
    val output = AnnotationLexer.apply(new StringReader(text)).toList
    val expected = List(AT_IDENT("type"), INLINE_STRING(" Int          => Int"))
    assert(expected == output)
  }

  test("regression") {
    // It should be also possible to write multiline strings in quotes.
    val text =
      """  \* TODO: use a model type here
        |  \* when #570 is closed: https://github.com/informalsystems/apalache/issues/570
        |  \* @type: Str;""".stripMargin
    val output = AnnotationLexer.apply(new StringReader(text)).toList
    val expected = List(IDENT("TODO"), AT_IDENT("type"), INLINE_STRING(" Str"))
    assert(expected == output)
  }

  test("annotation with ASCII codes") {
    // a sequence of control characters is replaced with a single space
    val text =
      "\\* @type: Int \t\f\r\n => Int;".stripMargin
    val output = AnnotationLexer.apply(new StringReader(text)).toList
    val expected = List(AT_IDENT("type"), INLINE_STRING(" Int  => Int"))
    assert(expected == output)
  }
}
