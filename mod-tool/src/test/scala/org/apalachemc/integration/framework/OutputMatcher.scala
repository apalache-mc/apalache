package org.apalachemc.integration.framework

import scala.annotation.tailrec

/** Normalizes CLI output and implements mdx-style whole-line ellipsis matching. */
object OutputMatcher {
  /** Normalizes line endings, trailing whitespace, and outer blank lines. */
  def normalize(text: String): String = {
    val normalizedLines = text
      .replace("\r\n", "\n")
      .replace('\r', '\n')
      .split("\n", -1)
      .toVector
      .map(_.replaceFirst("[ \\t]+$", ""))

    dropOuterBlankLines(normalizedLines).mkString("\n")
  }

  /** Matches output, treating a whole-line ellipsis as any number of lines. */
  def matches(expected: String, actual: String): Boolean = {
    val expectedLines = lines(normalize(expected))
    val actualLines = lines(normalize(actual))
    val startsWithWildcard = expectedLines.headOption.contains("...")
    val endsWithWildcard = expectedLines.lastOption.contains("...")
    val segments = expectedLines.foldLeft(Vector(Vector.empty[String])) { (all, line) =>
      if (line == "...") {
        if (all.last.isEmpty) all else all :+ Vector.empty
      } else {
        all.init :+ (all.last :+ line)
      }
    }.filter(_.nonEmpty)

    if (segments.isEmpty) {
      startsWithWildcard || actualLines.isEmpty
    } else {
      findSegments(actualLines, segments, startsWithWildcard, endsWithWildcard)
    }
  }

  /** Formats a diagnostic for output that failed template matching. */
  def mismatch(expected: String, actual: String, command: String): String = {
    s"""Output did not match for: $command
       |Whole-line '...' matches any number of output lines.
       |
       |--- expected ---
       |${normalize(expected)}
       |--- actual ---
       |${normalize(actual)}
       |--- end ---""".stripMargin
  }

  private def lines(text: String): Vector[String] = if (text.isEmpty) Vector.empty else text.split("\n", -1).toVector

  private def findSegments(
      actual: Vector[String],
      segments: Vector[Vector[String]],
      startsWithWildcard: Boolean,
      endsWithWildcard: Boolean): Boolean = {
    @tailrec
    def loop(segmentIndex: Int, from: Int, lastEnd: Int): Option[Int] = {
      if (segmentIndex == segments.length) {
        Some(lastEnd)
      } else {
        val segment = segments(segmentIndex)
        val foundAt =
          if (segmentIndex == 0 && !startsWithWildcard) {
            if (actual.startsWith(segment)) 0 else -1
          } else {
            findSlice(actual, segment, from)
          }

        if (foundAt < 0) None
        else loop(segmentIndex + 1, foundAt + segment.length, foundAt + segment.length)
      }
    }

    loop(0, 0, 0).exists(lastEnd => endsWithWildcard || lastEnd == actual.length)
  }

  private def findSlice(haystack: Vector[String], needle: Vector[String], from: Int): Int = {
    val lastStart = haystack.length - needle.length
    (from to lastStart).find(index => haystack.slice(index, index + needle.length) == needle).getOrElse(-1)
  }

  @tailrec
  private def dropLeadingBlankLines(lines: Vector[String]): Vector[String] = {
    if (lines.headOption.exists(_.isEmpty)) dropLeadingBlankLines(lines.tail) else lines
  }

  private def dropOuterBlankLines(lines: Vector[String]): Vector[String] = {
    dropLeadingBlankLines(dropLeadingBlankLines(lines.reverse).reverse)
  }
}
