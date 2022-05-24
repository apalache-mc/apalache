package at.forsyte.apalache.io.lir

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.values.TlaBool

import java.io.PrintWriter
import java.util.Calendar
import com.typesafe.scalalogging.LazyLogging

/**
 * A printer for counterexamples, in various formats: TLA+ , as TLC output, ...
 *
 * @author
 *   Andrey Kuprianov
 */
trait CounterexampleWriter {
  // Print out invariant violation
  def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]): Unit
}

class TlaCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {

  import CounterexampleWriter.stateToEx

  def printStateFormula(pretty: PrettyWriter, state: State): Unit =
    if (state.isEmpty) {
      pretty.write(ValEx(TlaBool(true)))
    } else {
      val prefix = if (state.size == 1) "" else "/\\ "
      state.toList.sortBy(_._1).foreach { case (name, value) =>
        writer.print(s"$prefix$name = ")
        pretty.write(value)
        writer.println()
      }
    }

  override def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]): Unit = {
    val pretty = new PrettyWriter(writer)

    pretty.writeHeader("counterexample", List(rootModule.name))

    states.zipWithIndex.foreach {
      case (state, 0) =>
        pretty.writeComment("Constant initialization state")
        val decl = tla.declOp("ConstInit", stateToEx(state._2))
        pretty.write(decl)
      case (state, j) =>
        // Index 0 is reserved for ConstInit, but users expect State0 to
        // be the initial state, so we shift indices by 1 for print-output
        val i = j - 1
        if (i == 0) {
          pretty.writeComment("Initial state")
        } else {
          pretty.writeComment(s"Transition ${state._1} to State$i")
        }
        val decl = tla.declOp(s"State$i", stateToEx(state._2))
        pretty.write(decl)
    }
    pretty.writeComment("The following formula holds true in the last state and violates the invariant")
    pretty.write(TlaOperDecl("InvariantViolation", List(), notInvariant))

    pretty.writeFooter()
    pretty.writeComment("Created by Apalache on %s".format(Calendar.getInstance().getTime))
    pretty.writeComment("https://github.com/informalsystems/apalache")
    pretty.close()
  }
}

class TlcCounterexampleWriter(writer: PrintWriter) extends TlaCounterexampleWriter(writer) {
  override def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]): Unit = {
    // `states` must always contain at least 1 state: the constant initialization
    // This makes `states.tail` safe, since we have a nonempty sequence
    assert(states.nonEmpty)

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

    states.zipWithIndex.tail.foreach { case (state, i) =>
      val prefix = if (i == 1) s"$i: <Initial predicate>" else s"$i: <Next>"

      writer.println(s"""@!@!@STARTMSG 2217:4 @!@!@
                        |$prefix""".stripMargin)
      // We still need to call PrettyWriter, since PrintWriter doesn't know how to output TlaEx
      printStateFormula(pretty, state._2)
      writer.println("""|
             |@!@!@ENDMSG 2217 @!@!@""".stripMargin)
    }
    pretty.close()
  }
}

class JsonCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {

  import CounterexampleWriter.stateToEx

  override def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]): Unit = {

    val tlaStates = states.zipWithIndex.collect { case (state, i) =>
      val name = i match {
        case 0 => "ConstInit"
        case _ => s"State${i - 1}"
      }
      tla.declOp(name, stateToEx(state._2)).withTag(Untyped)
    }

    val mod =
      new TlaModule("counterexample", tlaStates ++ List(TlaOperDecl(s"InvariantViolation", List(), notInvariant)))

    // No SourceLocator, since CEs aren't part of the spec
    val jsonText = new TlaToUJson(locatorOpt = None)(TlaType1PrinterPredefs.printer).makeRoot(Seq(mod)).toString
    writer.write(jsonText)

  }
}

object CounterexampleWriter extends LazyLogging {

  def stateToEx(state: State): TlaEx =
    if (state.isEmpty) {
      ValEx(TlaBool(true))
    } else {
      val namesAndVals = state.toSeq.sortBy(_._1).map { case (name, value) =>
        tla.eql(tla.name(name), value)
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
      suffix: String,
      rootModule: TlaModule,
      notInvariant: NotInvariant,
      states: List[NextState]): List[String] = {
    val writerHelper: String => PrintWriter => Unit =
      kind => writer => apply(kind, writer).write(rootModule, notInvariant, states)

    val fileNames = List(
        ("tla", s"counterexample$suffix.tla"),
        ("tlc", s"MC$suffix.out"),
        ("json", s"counterexample$suffix.json"),
        ("itf.json", s"counterexample$suffix.itf.json"),
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
