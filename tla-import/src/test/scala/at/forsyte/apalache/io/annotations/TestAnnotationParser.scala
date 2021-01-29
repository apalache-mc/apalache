package at.forsyte.apalache.io.annotations

import at.forsyte.apalache.io.annotations.AnnotationParser.{Failure, Success}
import org.junit.runner.RunWith
import org.scalacheck.Arbitrary.arbitrary
import org.scalacheck.Gen.{alphaNumStr, alphaStr, identifier, listOf, oneOf}
import org.scalacheck.Prop.{AnyOperators, falsified, forAll, passed}
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import org.scalatest.prop.Checkers

@RunWith(classOf[JUnitRunner])
class TestAnnotationParser extends FunSuite with Checkers {
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
    AnnotationParser.parse("") match {
      case AnnotationParser.Failure(_) =>
        ()
    }
  }

  test("test on one-line input") {
    val expected =
      new Annotation(
          "greet",
          TlaAnnotationString("hello"),
          TlaAnnotationInt(2021),
          TlaAnnotationBool(true)
      )
    AnnotationParser.parse("""  @greet("hello", 2021, true)   """) match {
      case AnnotationParser.Success(parsed, _) =>
        assert(expected == parsed)
    }
  }

  test("test the special form of a one-argument annotation") {
    val expected =
      new Annotation(
          "type",
          TlaAnnotationString("(Int, Int) -> Set(Int) ")
      )
    AnnotationParser.parse("""  @type: (Int, Int) -> Set(Int) ;""") match {
      case AnnotationParser.Success(parsed, _) =>
        assert(expected.toPrettyString == parsed.toPrettyString)
    }
  }

  test("test on multiline input") {
    val expected =
      new Annotation(
          "greet",
          TlaAnnotationString("hello"),
          TlaAnnotationInt(2021),
          TlaAnnotationBool(true)
      )
    val text =
      """  @greet("hello",
        |         2021,
        |         true)     """.stripMargin
    AnnotationParser.parse(text) match {
      case AnnotationParser.Success(parsed, _) =>
        assert(expected == parsed)
    }
  }

  // For some reason, if there is a bug in the parser, e.g., comment out boolArg in TlaAnnotationParser.arg),
  // then the shrinker produces a useless empty test.
  // Disable the shrinker.
  import org.scalacheck.Shrink.shrinkAny

  test("parse OK on random good inputs @foo(arg1, ..., argN)") {
    check(
        {
          forAll(identifier) { name =>
            forAll(listOf(oneOf(genStr, genInt, genBool))) { args =>
              val annotation = new Annotation(name, args: _*)
              AnnotationParser.parse(annotation.toString) match {
                case AnnotationParser.Success(parsed, _) =>
                  annotation ?= parsed

                case AnnotationParser.Failure(_) =>
                  falsified
              }
            }
          }
        },
        minSuccessful(200)
    )
  }

  test("parse error on random bad inputs") {
    check(
        {
          forAll(alphaStr) { str =>
            AnnotationParser.parse(str) match {
              // Pass the test on successful parse.
              // To see how testing is different from verification,
              // replace 'passed' with 'falsified' and observe that no error will be found ;-)
              case Success(_, _) => passed

              case Failure(_) => passed
            }
          // no exceptions
          }
        },
        minSuccessful(300)
    )
  }
}
