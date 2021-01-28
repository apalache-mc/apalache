package at.forsyte.apalache.io.annotations

import at.forsyte.apalache.io.annotations.TlaAnnotationParser.{Failure, Success}
import org.junit.runner.RunWith
import org.scalacheck.Arbitrary.arbitrary
import org.scalacheck.Gen.{alphaNumStr, alphaStr, identifier, listOf, oneOf}
import org.scalacheck.Prop.{AnyOperators, falsified, forAll, passed}
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers

@RunWith(classOf[JUnitRunner])
class TestTlaAnnotationParser extends FunSuite with Checkers {
  // generators for the case classes
  private val genStr = for {
    // I would like to check a string that contains ASCII characters, but not the quotes (").
    // Unfortunately, suchThat is too imprecise for that as scalacheck is giving up too quickly.
    // Hence, check only alpha-numeric strings.
    text <- alphaNumStr
  } yield TlaAnnotationString(text)

  private val genInt = for {
    i <- arbitrary[Int]
  } yield TlaAnnotationInt(i)

  private val genBool = for {
    b <- arbitrary[Boolean]
  } yield TlaAnnotationBool(b)


  test("test on empty input") {
    TlaAnnotationParser.parse("") match {
      case TlaAnnotationParser.Failure(_) =>
        ()
    }
  }

  test("test on one-line input") {
    val expected =
      new TlaAnnotation("greet", TlaAnnotationString("hello"), TlaAnnotationInt(2021), TlaAnnotationBool(true))
    TlaAnnotationParser.parse("""  @greet("hello", 2021, true)   """) match {
      case TlaAnnotationParser.Success(parsed, _) =>
        assert(expected == parsed)
    }
  }

  test("test on multiline input") {
    val expected =
      new TlaAnnotation("greet", TlaAnnotationString("hello"), TlaAnnotationInt(2021), TlaAnnotationBool(true))
    val text =
      """  @greet("hello",
        |         2021,
        |         true)     """.stripMargin
    TlaAnnotationParser.parse(text) match {
      case TlaAnnotationParser.Success(parsed, _) =>
        assert(expected == parsed)
    }
  }

  // For some reason, if there is a bug in the parser, e.g., comment out boolArg in TlaAnnotationParser.arg),
  // then the shrinker produces a useless empty test.
  // Disable the shrinker.
  import org.scalacheck.Shrink.shrinkAny

  test("parse OK on random good inputs @foo(arg1, ..., argN)") {
    check({
      forAll(identifier) { name =>
        forAll(listOf(oneOf(genStr, genInt, genBool))) { args =>
          val annotation = new TlaAnnotation(name, args: _*)
          TlaAnnotationParser.parse(annotation.toString) match {
            case TlaAnnotationParser.Success(parsed, _) =>
              annotation ?= parsed

            case TlaAnnotationParser.Failure(_) =>
              falsified
          }
        }
      }
    }, minSuccessful(200))
  }

  test("parse error on random bad inputs") {
    check({
      forAll(alphaStr) { str =>
          TlaAnnotationParser.parse(str) match {
            // Pass the test on successful parse.
            // To see how testing is different from verification,
            // replace 'passed' with 'falsified' and observe that no error will be found ;-)
            case Success(_, _) => passed

            case Failure(_) => passed
          }
          // no exceptions
      }
    }, minSuccessful(300))
  }
}
