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
  def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]) : Unit
}

object CounterexampleWriter {
  // default implementation -- write in all formats, and return the list of files written
  def writeAllFormats(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState] ): List[String] = {
    val fileNames = Map(
      "tla" -> "counterexample.tla",
      "tlc" -> "MC.out",
      "json" -> "counterexample.json"
    )
    val files = fileNames.map {
      case (kind, name) => (kind, new PrintWriter(new FileWriter(name)))
    }
    try {
      files.foreach {
        case (kind, writer) => apply(kind, writer).write(rootModule, notInvariant, states)
      }
      fileNames.values.toList
    }
    finally {
      files.foreach {
        case (_, writer) => writer.close()
      }
    }
  }

  // factory method to get the desired CE writer
  def apply(kind: String, writer: PrintWriter): CounterexampleWriter = {
    kind match {
      case "tla" => new TlaCounterexampleWriter(writer)
      case "tlc" => new TlcCounterexampleWriter(writer)
      case "json" => new JsonCounterexampleWriter(writer)
      case _ => throw new Exception("unknown couterexample writer requested")
    }
  }
}

class TlaCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {

  def printStateFormula(pretty: PrettyWriter, state: State) = {
    if (state.isEmpty) {
      pretty.write(ValEx(TlaBool(true)))
    } else {
      state.toList.sortBy(_._1).foreach{
        case (name,value) =>
          writer.print(s"/\\ $name = " )
          pretty.write(value)
          writer.println
      }
    }
  }

  override def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState] ) : Unit = {
    val pretty = new PrettyWriter(writer)

    writer.println("%s MODULE counterexample %s\n".format("-" * 25, "-" * 25))
    writer.println("EXTENDS %s\n".format(rootModule.name))

    states.zipWithIndex.foreach {
      case (state, j) =>
        val i = j+1 // start counting from 1, for compatibility with TLC counterexamples
        if(i == 1) {
          writer.println("(* Initial state *)")
        }
        else {
          writer.println(s"(* Transition ${state._1} to State$i *)")
        }
        writer.println(s"\nState$i ==")
        printStateFormula(pretty, state._2)
        writer.println
    }
    writer.print(
      s"""(* The following formula holds true in the last state and violates the invariant *)
         |
         |""".stripMargin)
    pretty.write(TlaOperDecl("InvariantViolation", List(), notInvariant))

    writer.println("\n\n%s".format("=" * 80))
    writer.println("\\* Created by Apalache on %s".format(Calendar.getInstance().getTime))
    writer.println("\\* https://github.com/konnov/apalache")
    writer.close()
  }
}


class TlcCounterexampleWriter(writer: PrintWriter) extends TlaCounterexampleWriter(writer) {

  override def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]): Unit = {
    writer.print(
      s"""@!@!@STARTMSG 2262:0 @!@!@
         |Created by Apalache on ${Calendar.getInstance().getTime}
         |@!@!@ENDMSG 2262 @!@!@
         |@!@!@STARTMSG 2110:1 @!@!@
         |Invariant is violated.
         |@!@!@ENDMSG 2110 @!@!@
         |@!@!@STARTMSG 2121:1 @!@!@
         |The behavior up to this point is:
         |@!@!@ENDMSG 2121 @!@!@
         |""".stripMargin)

    states.zipWithIndex.foreach {
      case (state, j) =>
        val i = j + 1 // start counting from 1, for compatibility with TLC counterexamples
        val prefix = if(i==1) s"$i: <Initial predicate>" else s"$i: <Next>"

        writer.println(
          s"""@!@!@STARTMSG 2217:4 @!@!@
             |$prefix""".stripMargin)
        printStateFormula(new PrettyWriter(writer), state._2)
        writer.println(
          """|
             |@!@!@ENDMSG 2217 @!@!@""".stripMargin)
    }
    writer.close()
  }
}

class JsonCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {
  override def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState] ) : Unit = {
    val json = new JsonWriter(writer)

    val tlaStates = states.zipWithIndex.collect{
      case ((tran,vars), i) =>
        val state = vars.collect{
          case (name,value) => OperEx(TlaOper.eq, NameEx(name), value)
        }
        TlaOperDecl(s"State${i+1}", List(), OperEx(TlaBoolOper.and, state.toList: _*))

    }

    val mod = new TlaModule(
      "counterexample",
      tlaStates ++ List(TlaOperDecl(s"InvariantViolation", List(), notInvariant)))
    json.write(mod)
  }
}
