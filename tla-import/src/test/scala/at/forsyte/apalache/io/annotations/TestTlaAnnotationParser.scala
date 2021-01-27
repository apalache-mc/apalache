package at.forsyte.apalache.io.annotations

import org.junit.runner.RunWith
import org.scalacheck.Arbitrary.arbitrary
import org.scalacheck.Gen.{alphaNumStr, alphaStr, identifier, listOf, oneOf}
import org.scalacheck.Prop.{AnyOperators, falsified, forAll, passed}
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers

@RunWith(classOf[JUnitRunner])
class TestTlaAnnotationParser extends FunSuite with Checkers {
  test("test on empty input") {
    assertThrows[TlaAnnotationParserError](TlaAnnotationParser(""))
  }

  test("test on one-line input") {
    val expected =
      new TlaAnnotation("greet", TlaAnnotationString("hello"), TlaAnnotationInt(2021), TlaAnnotationBool(true))
    val parsed = TlaAnnotationParser("""  @greet("hello", 2021, true)   """)
    assert(expected == parsed)
  }

  test("test on multiline input") {
    val expected =
      new TlaAnnotation("greet", TlaAnnotationString("hello"), TlaAnnotationInt(2021), TlaAnnotationBool(true))
    val text =
      """  @greet("hello",
        |         2021,
        |         true)     """.stripMargin
    val parsed = TlaAnnotationParser(text)
    assert(expected == parsed)
  }

  // For some reason, if there is a bug in the parser, e.g., comment out boolArg in TlaAnnotationParser.arg),
  // then the shrinker produces a useless empty test.
  // Disable the shrinker.
  import org.scalacheck.Shrink.shrinkAny

  test("parse OK on random good inputs") {
    val genStr = for {
      // I would like to check a string that contains ASCII characters, but not the quotes (").
      // Unfortunately, suchThat is too imprecise for that as scalacheck is giving up too quickly.
      // Hence, check only alpha-numeric strings.
      text <- alphaNumStr
    } yield TlaAnnotationString(text)
    val genInt = for {
      i <- arbitrary[Int]
    } yield TlaAnnotationInt(i)
    val genBool = for {
      b <- arbitrary[Boolean]
    } yield TlaAnnotationBool(b)
    check({
      forAll(identifier) { name =>
        forAll(listOf(oneOf(genStr, genInt, genBool))) { args =>
          val annotation = new TlaAnnotation(name, args: _*)
          annotation ?= TlaAnnotationParser(annotation.toString)
        }
      }
    }, minSuccessful(200))
  }

  test("parse error on random bad inputs") {
    check({
      forAll(alphaStr) { str =>
        try {
          TlaAnnotationParser(str)
          // Pass the test on successful parse.
          // To see how testing is different from verification,
          // replace 'passed' with 'falsified' and observe that no error will be found ;-)
          passed
        } catch {
          // a parser error is also OK
          case _: TlaAnnotationParserError => passed
          // other exceptions are not OK
          case _ => falsified
        }
      }
    }, minSuccessful(300))
  }
}
