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
  private def expectOk(expectedTokens: List[AnnotationToken], inputText: String) = {
    AnnotationLexer(new StringReader(inputText))
      .map(output => assert(expectedTokens == output))
      .swap
      .map(r => fail("Unexpected lexer error: " + r))
  }

  private def expectError(inputText: String) = {
    AnnotationLexer(new StringReader(inputText))
      .map(r => fail("Expected lexer error. Found: " + r))
  }

  test("empty") {
    val text = "   "
    expectError(text)
  }

  test("@test without arguments") {
    val text = "  @test  "
    val expected = List(AT_IDENT("test"))
    expectOk(expected, text)
  }

  test("@test surrounded by junk") {
    val text = "(*  @test *)"
    expectError(text)
  }

  test("@test(123, TRUE)") {
    val text = "  @test(123, TRUE) "
    val expected = List(AT_IDENT("test"), LPAREN(), NUMBER(123), COMMA(), BOOLEAN(true), RPAREN())
    expectOk(expected, text)
  }

  test("an annotation surrounded by some text") {
    // This should report an error. We are using CommentPreprocessor to fish for annotations in the sea of junk.
    val text = """\* example by foo@example.org: @test(123, TRUE) the rest is junk. :-)"""
    expectError(text)
  }

  test("identifier argument") {
    val text = """@foo(Bar)"""
    val expected = List(AT_IDENT("foo"), LPAREN(), IDENT("Bar"), RPAREN())
    expectOk(expected, text)
  }

  test("string argument") {
    val text = """@foo("one", "two")"""
    val expected =
      List(AT_IDENT("foo"), LPAREN(), STRING("one"), COMMA(), STRING("two"), RPAREN())
    expectOk(expected, text)
  }

  test("inline string argument") {
    val text = """@baz: one;"""
    val expected = List(AT_IDENT("baz"), INLINE_STRING(" one"))
    expectOk(expected, text)
  }

  test("mismatch in a string") {
    // it is a job of CommentPreprocessor to feed us with proper annotations
    val text = """ 1.3 " zzz """
    expectError(text)
  }

  test("annotation with comments inside") {
    // it is a job of CommentPreprocessor to feed us with proper annotations
    val text =
      """\* @type: Int
      |\*          => Int;""".stripMargin
    expectError(text)
  }

  test("regression") {
    // it is a job of CommentPreprocessor to feed us with proper annotations
    val text =
      """  \* TODO: use a model type here
        |  \* when #570 is closed: https://github.com/informalsystems/apalache/issues/570
        |  \* @type: Str;""".stripMargin
    expectError(text)
  }

  test("annotation with ASCII codes") {
    // a sequence of control characters is replaced with a single space
    val text =
      " @type: Int \t\f\r\n => Int;".stripMargin
    val expected = List(AT_IDENT("type"), INLINE_STRING(" Int => Int"))
    expectOk(expected, text)
  }
}
