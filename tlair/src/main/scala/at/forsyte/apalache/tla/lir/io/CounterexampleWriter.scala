package at.forsyte.apalache.tla.lir.io

import java.io.{FileWriter, PrintWriter}
import java.util.Calendar

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._

/**
 * A printer for counterexamples, in various formats: TLA+ , as TLC output, ...
 *
 * @author Andrey Kuprianov
 */
trait CounterexampleWriter {
  // Print out invariant violation
  def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]): Unit
}

object CounterexampleWriter {
  // default implementation -- write in all formats, and return the list of files written
  def writeAllFormats(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]): List[String] = {
    val fileNames = Map(
        "tla" -> "counterexample.tla",
        "tlc" -> "MC.out",
        "json" -> "counterexample.json"
    )
    val files = fileNames.map { case (kind, name) =>
      (kind, new PrintWriter(new FileWriter(name)))
    }
    try {
      files.foreach { case (kind, writer) =>
        apply(kind, writer).write(rootModule, notInvariant, states)
      }
      fileNames.values.toList
    } finally {
      files.foreach { case (_, writer) =>
        writer.close()
      }
    }
  }

  // factory method to get the desired CE writer
  def apply(kind: String, writer: PrintWriter): CounterexampleWriter = {
    kind match {
      case "tla"  => new TlaCounterexampleWriter(writer)
      case "tlc"  => new TlcCounterexampleWriter(writer)
      case "json" => new JsonCounterexampleWriter(writer)
      case _      => throw new Exception("unknown couterexample writer requested")
    }
  }
}

class TlaCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {
  def printStateFormula(pretty: PrettyWriter, state: State): Unit = {
    if (state.isEmpty) {
      pretty.write(ValEx(TlaBool(true)))
      pretty.writeln()
    } else {
      state.toList.sortBy(_._1).foreach { case (name, value) =>
        pretty.write(s"/\\ $name = ")
        pretty.write(value)
        pretty.writeln()
      }
    }
  }

  override def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]): Unit = {
    val pretty = new PrettyWriter(writer)

    pretty.prettyWriteDoc(pretty.moduleNameDoc("counterexample", 25))
    pretty.writeln()
    pretty.prettyWriteDoc(pretty.moduleExtendsDoc(rootModule.name))
    pretty.writeln()

    states.zipWithIndex.foreach {
      case (state, 0) =>
        pretty.writeln("(* Constant initialization state *)")
        pretty.writeln(s"\nConstInit ==")
        printStateFormula(pretty, state._2)
        pretty.writeln()
      case (state, j) =>
        // Index 0 is reserved for ConstInit, but users expect State0 to
        // be the initial state, so we shift indices by 1 for print-output
        val i = j - 1
        if (i == 0) {
          pretty.writeln("(* Initial state *)")
        } else {
          pretty.writeln(s"(* Transition ${state._1} to State$i *)")
        }
        pretty.writeln(s"\nState$i ==")
        printStateFormula(pretty, state._2)
        pretty.writeln()
    }
    pretty.write(s"""(* The following formula holds true in the last state and violates the invariant *)
                    |
                    |""".stripMargin)
    pretty.write(TlaOperDecl("InvariantViolation", List(), notInvariant))

    pretty.writeln()
    pretty.writeln()
    pretty.prettyWriteDoc(pretty.moduleTerminalDoc(80))
    pretty.writeln("\\* Created by Apalache on %s".format(Calendar.getInstance().getTime))
    pretty.writeln("\\* https://github.com/informalsystems/apalache")
    pretty.close()
  }
}

class TlcCounterexampleWriter(writer: PrintWriter) extends TlaCounterexampleWriter(writer) {
  override def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]): Unit = {
    // `states` must always contain at least 1 state: the constant initialization
    // This makes `states.tail` safe, since we have a nonempty sequence
    assert(states.nonEmpty)

    val pretty = new PrettyWriter(writer)

    pretty.write(s"""@!@!@STARTMSG 2262:0 @!@!@
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

      pretty.writeln(s"""@!@!@STARTMSG 2217:4 @!@!@
                        |$prefix""".stripMargin)
      printStateFormula(pretty, state._2)
      pretty.writeln("""|
             |@!@!@ENDMSG 2217 @!@!@""".stripMargin)
    }
    pretty.close()
  }
}

class JsonCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {
  override def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]): Unit = {
    val json = new JsonWriter(writer)

    val tlaStates = states.zipWithIndex.collect { case ((_, vars), i) =>
      val state = vars.collect { case (name, value) =>
        OperEx(TlaOper.eq, NameEx(name), value)
      }
      val name = i match {
        case 0 => "ConstInit"
        case _ => s"State${i - 1}"
      }
      TlaOperDecl(name, List(), OperEx(TlaBoolOper.and, state.toList: _*))

    }

    val mod =
      new TlaModule("counterexample", tlaStates ++ List(TlaOperDecl(s"InvariantViolation", List(), notInvariant)))
    json.write(mod)
  }
}
