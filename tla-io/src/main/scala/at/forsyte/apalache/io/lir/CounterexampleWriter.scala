package at.forsyte.apalache.io.lir

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.tla.typecomp.{build, TBuilderInstruction}
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import com.typesafe.scalalogging.LazyLogging

import java.io.PrintWriter
import java.util.Calendar

/**
 * A printer for counterexamples, in various formats: TLA+ , as TLC output, ...
 *
 * @author
 *   Andrey Kuprianov
 */
trait CounterexampleWriter {
  // Print out invariant violation
  def write(trace: Trace[TlaEx]): Unit
}

class TlaCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {

  import CounterexampleWriter.stateToEx

  def printStateFormula(pretty: PrettyWriter, state: Trace.State): Unit =
    if (state.isEmpty) {
      pretty.write(tla.bool(true))
    } else {
      val prefix = if (state.size == 1) "" else "/\\ "
      state.toList.sortBy(_._1).foreach { case (name, value) =>
        writer.print(s"$prefix$name = ")
        pretty.write(value)
        writer.println()
      }
    }

  override def write(trace: Trace[TlaEx]): Unit = {
    val pretty = new PrettyWriter(writer)
    pretty.writeHeader("counterexample", List(trace.module.name))

    trace.states.zip(trace.labels).zipWithIndex.foreach {
      case ((state, labels), 0) =>
        val labels_s = if (labels.isEmpty) "" else labels.toList.mkString(" [", ", ", "]")
        pretty.writeComment(s"Constant initialization state$labels_s")
        val decl = tla.decl("ConstInit", stateToEx(state))
        pretty.write(decl)
      case ((state, labels), j) =>
        // Index 0 is reserved for ConstInit, but users expect State0 to
        // be the initial state, so we shift indices by 1 for print-output
        val i = j - 1
        val labels_str = if (labels.isEmpty) "" else labels.toList.mkString(" [", ", ", "]")
        if (i == 0) {
          pretty.writeComment(s"Initial state$labels_str")
        } else {
          pretty.writeComment(s"State$i$labels_str")
        }
        val decl = tla.decl(s"State$i", stateToEx(state))
        pretty.writeWithNameReplacementComment(decl)
    }
    pretty.writeComment("The following formula holds true in the last state and violates the invariant")
    pretty.writeWithNameReplacementComment(tla.decl("InvariantViolation", tla.unchecked(trace.data)))

    pretty.writeFooter()
    pretty.writeComment("Created by Apalache on %s".format(Calendar.getInstance().getTime))
    pretty.writeComment("https://github.com/apalache-mc/apalache")
    pretty.close()
  }
}

class TlcCounterexampleWriter(writer: PrintWriter) extends TlaCounterexampleWriter(writer) {
  override def write(trace: Trace[TlaEx]): Unit = {
    // `states` must always contain at least 1 state: the constant initialization
    // This makes `states.tail` safe, since we have a nonempty sequence
    assert(trace.states.nonEmpty)

    val pretty = new PrettyWriter(writer)

    writer.write(s"""@!@!@STARTMSG 2262:0 @!@!@
                    |Created by Apalache on ${Calendar.getInstance().getTime}
                    |@!@!@ENDMSG 2262 @!@!@
                    |@!@!@STARTMSG 2110:1 @!@!@
                    |Invariant is violated.
                    |@!@!@ENDMSG 2110 @!@!@
                    |@!@!@STARTMSG 2121:1 @!@!@
                    |The behavior up to this point is:
                    |@!@!@ENDMSG 2121 @!@!@
                    |""".stripMargin)

    trace.states.zipWithIndex.tail.foreach { case (state, i) =>
      val prefix = if (i == 1) s"$i: <Initial predicate>" else s"$i: <Next>"

      writer.println(s"""@!@!@STARTMSG 2217:4 @!@!@
                        |$prefix""".stripMargin)
      // We still need to call PrettyWriter, since PrintWriter doesn't know how to output TlaEx
      printStateFormula(pretty, state)
      writer.println("""|
             |@!@!@ENDMSG 2217 @!@!@""".stripMargin)
    }
    pretty.close()
  }
}

class JsonCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {

  import CounterexampleWriter.stateToEx

  override def write(trace: Trace[TlaEx]): Unit = {
    val tlaStates = trace.states.zipWithIndex.collect { case (state, i) =>
      val name = i match {
        case 0 => "ConstInit"
        case _ => s"State${i - 1}"
      }
      tla.decl(name, stateToEx(state))
    }

    val operDecls = (tlaStates :+ tla.decl("InvariantViolation", tla.unchecked(trace.data))).map(build)

    val mod = TlaModule("counterexample", operDecls)

    // No SourceLocator, since CEs aren't part of the spec
    val jsonText = new TlaToUJson(locatorOpt = None)(TlaType1PrinterPredefs.printer).makeRoot(Seq(mod)).toString
    writer.write(jsonText)
  }
}

object CounterexampleWriter extends LazyLogging {

  def stateToEx(state: Trace.State): TBuilderInstruction =
    if (state.isEmpty) {
      tla.bool(true)
    } else {
      val namesAndVals = state.toSeq.sortBy(_._1).map { case (name, value) =>
        tla.eql(tla.name(name, value.typeTag.asTlaType1()), tla.unchecked(value))
      }
      tla.and(namesAndVals: _*)
    }

  /**
   * Write a counterexample in all supported formats (TLA+, MC.out, JSON), and return the list of files written.
   *
   * @param suffix
   *   suffix to be added in the end of a filename, may be empty
   * @param rootModule
   *   source module of the counterexample
   * @param notInvariant
   *   negated invariant
   * @param states
   *   sequence of states that represent the counterexample
   */
  def writeAllFormats(
      prefix: String,
      suffix: String,
      trace: Trace[TlaEx]): List[String] = {
    val writerHelper: String => PrintWriter => Unit =
      kind => writer => apply(kind, writer).write(trace)

    val fileNames = List(
        ("tla", s"$prefix$suffix.tla"),
        ("tlc", s"MC$prefix$suffix.out"),
        ("json", s"$prefix$suffix.json"),
        ("itf.json", s"$prefix$suffix.itf.json"),
    )

    fileNames.flatMap { case (kind, name) =>
      if (OutputManager.withWriterInRunDir(name)(writerHelper(kind))) {
        Some(OutputManager.runDir.resolve(name).normalize.toString)
      } else {
        None
      }
    }
  }

  // factory method to get the desired CE writer
  def apply(kind: String, writer: PrintWriter): CounterexampleWriter = {
    kind match {
      case "tla"      => new TlaCounterexampleWriter(writer)
      case "tlc"      => new TlcCounterexampleWriter(writer)
      case "json"     => new JsonCounterexampleWriter(writer)
      case "itf.json" => new ItfCounterexampleWriter(writer)
      case fmt        => throw new Exception(s"unknown counterexample format requested: $fmt")
    }
  }
}
